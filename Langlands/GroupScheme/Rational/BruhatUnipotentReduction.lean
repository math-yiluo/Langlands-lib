import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.PointDecomposition

/-! # Passage from unipotent normalizer separation to rational Bruhat separation -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Normalizing points are unique within every unipotent double coset. This
is an intermediate geometric assertion, not an additional hypothesis in the
published rational Bruhat statement. -/
def HasUnipotentNormalizerSeparation : Prop :=
  ∀ (n n' : normalizerPoints i)
    (u : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i))
    (v : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)),
    (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = u * n * v → n' = n

/-- A Levi/whole-torus-centralizer equality identifies the two rational-point
subgroups used in the unipotent reduction. -/
theorem rationalLevi_eq_centralizerPoints_of_eq
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i) :
    RationalPoint.levi (CommGroupScheme.groupHom ν ≫ i) = centralizerPoints i := by
  change (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) = _
  rw [hZ, torusCentralizer_carrier_base]

variable [IsAffineHom G.X.hom]

/-- The two Levi factorizations turn a parabolic double-coset equality between
normalizing points into a unipotent double-coset equality. Unipotent uniqueness
therefore gives equality of the relative Weyl classes. -/
theorem relativeWeyl_eq_of_parabolic_mul_of_unipotent_separation
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hsep : HasUnipotentNormalizerSeparation i ν)
    (n n' : normalizerPoints i)
    (p q : RationalPoint.parabolic (CommGroupScheme.groupHom ν ≫ i))
    (heq : (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = p * n * q) :
    (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n' := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  obtain ⟨⟨u, a⟩, ⟨hu, ha, hp⟩, _⟩ :=
    RationalPoint.existsUnique_unipotent_mul_levi χ p.property
  obtain ⟨⟨b, v⟩, ⟨hb, hv, hq⟩, _⟩ :=
    RationalPoint.existsUnique_levi_mul_unipotent χ q.property
  have hZpts := rationalLevi_eq_centralizerPoints_of_eq i ν hZ
  have haZ : a ∈ centralizerPoints i := hZpts ▸ ha
  have hbZ : b ∈ centralizerPoints i := hZpts ▸ hb
  let aN : normalizerPoints i := ⟨a, centralizerPoints_le_normalizerPoints i haZ⟩
  let bN : normalizerPoints i := ⟨b, centralizerPoints_le_normalizerPoints i hbZ⟩
  have hnn' : n' = aN * n * bN := by
    apply hsep (aN * n * bN) n' ⟨u, hu⟩ ⟨v, hv⟩
    simpa only [hp, hq, aN, bN, Subgroup.coe_mul, mul_assoc] using heq
  have ha1 : (QuotientGroup.mk aN : relativeWeylGroup i) = 1 :=
    (QuotientGroup.eq_one_iff aN).mpr haZ
  have hb1 : (QuotientGroup.mk bN : relativeWeylGroup i) = 1 :=
    (QuotientGroup.eq_one_iff bN).mpr hbZ
  rw [hnn', QuotientGroup.mk_mul, QuotientGroup.mk_mul, ha1, hb1, one_mul, mul_one]

/-- Under the generic-centralizer identity, the geometric unipotent covering
and normalizer separation assertions imply the full published Bruhat predicate. -/
theorem hasRationalBruhatDecomposition_of_unipotent_covering_and_separation
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ (n : normalizerPoints i)
        (u v : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)),
        g = u * n * v)
    (hsep : HasUnipotentNormalizerSeparation i ν) :
    HasRationalBruhatDecomposition i ν := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  refine ⟨?_, ?_⟩
  · intro g
    obtain ⟨n, u, v, heq⟩ := hcover g
    exact ⟨n.val, n.property, u.val, RationalPoint.unipotent_le_parabolic χ u.property,
      v.val, RationalPoint.unipotent_le_parabolic χ v.property, heq⟩
  · intro n n'
    constructor
    · rintro ⟨p, hp, q, hq, heq⟩
      exact relativeWeyl_eq_of_parabolic_mul_of_unipotent_separation i ν hZ hsep n n'
        ⟨p, hp⟩ ⟨q, hq⟩ heq
    · intro h
      have hz : (n⁻¹ * n' : normalizerPoints i) ∈
          (centralizerPoints i).subgroupOf (normalizerPoints i) :=
        QuotientGroup.eq.mp h
      have hzP : (n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * n' ∈ RationalPoint.parabolic χ := by
        apply RationalPoint.levi_le_parabolic χ
        rwa [rationalLevi_eq_centralizerPoints_of_eq i ν hZ]
      exact ⟨1, Subgroup.one_mem _, _, hzP, by simp⟩

end Langlands.GroupScheme
