import Langlands.GroupScheme.Rational.Statement
import Mathlib.GroupTheory.DoubleCoset

/-! # The canonical map from the relative Weyl group to rational double cosets -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Whole-torus centralizer points belong to the dynamic parabolic of every
cocharacter through the torus. -/
theorem centralizerPoints_le_dynamicParabolic {S : Scheme.{u}}
    {T : CommGroupScheme S} {G : GroupScheme S} (i : T.toGrp ⟶ G)
    (χ : (Gm S).toGrp ⟶ T.toGrp) :
    centralizerPoints i ≤ (Dynamic.parabolic (χ ≫ i)).carrier (Over.mk (𝟙 S)) := by
  intro g hg
  apply Dynamic.centralizer_le_parabolic (χ ≫ i) _ _
  apply torusCentralizer_le_dynamicCentralizer i χ _ _
  change g ∈ (torusCentralizer i).carrier (Over.mk (𝟙 S))
  rwa [torusCentralizer_carrier_base]

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Equality of relative Weyl classes is membership of the quotient of
normalizing points in the whole-torus centralizer. -/
theorem relativeWeyl_eq_iff_inv_mul_mem_centralizerPoints (n n' : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n' ↔
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ * n' ∈
        centralizerPoints i :=
  QuotientGroup.eq

/-- Equal relative Weyl classes always give the same rational parabolic double
coset; this direction requires no reductivity or genericity. -/
theorem exists_parabolic_mul_of_relativeWeyl_eq (n n' : normalizerPoints i)
    (h : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n') :
    ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
      ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = p * n * q := by
  refine ⟨1, Subgroup.one_mem _, (n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * n', ?_, ?_⟩
  · exact centralizerPoints_le_dynamicParabolic i (CommGroupScheme.groupHom ν)
      ((relativeWeyl_eq_iff_inv_mul_mem_centralizerPoints i n n').mp h)
  · simp

/-- The actual rational double-coset space for the dynamic parabolic of `ν`. -/
abbrev rationalBruhatDoubleCosets : Type u :=
  DoubleCoset.Quotient
    ((Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    ((Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))

/-- The canonical map `N(k)/Z(k) → P(k)\G(k)/P(k)`. -/
def relativeWeylToDoubleCosets : relativeWeylGroup i → rationalBruhatDoubleCosets i ν :=
  Quotient.lift
    (fun n : normalizerPoints i => DoubleCoset.mk _ _ n.val)
    (fun n n' h => DoubleCoset.eq.mpr
      (exists_parabolic_mul_of_relativeWeyl_eq i ν n n' (Quotient.sound h)))

@[simp]
theorem relativeWeylToDoubleCosets_mk (n : normalizerPoints i) :
    relativeWeylToDoubleCosets i ν (QuotientGroup.mk n) = DoubleCoset.mk _ _ n.val :=
  rfl

/-- Surjectivity of the canonical map is exactly covering by the rational
parabolic double cosets of normalizing points. -/
theorem relativeWeylToDoubleCosets_surjective_iff :
    Function.Surjective (relativeWeylToDoubleCosets i ν) ↔
      ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, ∃ n ∈ normalizerPoints i,
        ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
          ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
            g = p * n * q := by
  constructor
  · intro h g
    obtain ⟨w, hw⟩ := h (DoubleCoset.mk _ _ g)
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨p, hp, q, hq, heq⟩ := DoubleCoset.eq.mp hw
    exact ⟨n.val, n.property, p, hp, q, hq, heq⟩
  · intro h c
    refine Quotient.inductionOn c ?_
    intro g
    obtain ⟨n, hn, p, hp, q, hq, heq⟩ := h g
    exact ⟨QuotientGroup.mk ⟨n, hn⟩, DoubleCoset.eq.mpr ⟨p, hp, q, hq, heq⟩⟩

/-- The published rational Bruhat predicate is equivalent to bijectivity of
the canonical map from the actual relative Weyl quotient. -/
theorem hasRationalBruhatDecomposition_iff_bijective :
    HasRationalBruhatDecomposition i ν ↔
      Function.Bijective (relativeWeylToDoubleCosets i ν) := by
  constructor
  · rintro ⟨hcover, hsep⟩
    refine ⟨?_, (relativeWeylToDoubleCosets_surjective_iff i ν).mpr hcover⟩
    intro w w' heq
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective w'
    exact (hsep n n').mp (DoubleCoset.eq.mp heq)
  · rintro ⟨hinj, hsurj⟩
    refine ⟨(relativeWeylToDoubleCosets_surjective_iff i ν).mp hsurj, ?_⟩
    intro n n'
    constructor
    · intro h
      exact hinj (DoubleCoset.eq.mpr h)
    · exact exists_parabolic_mul_of_relativeWeyl_eq i ν n n'

end Langlands.GroupScheme
