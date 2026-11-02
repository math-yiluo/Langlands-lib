import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Rational conjugacy and transport of standard-parabolic indices -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Pulling back along an isomorphism and then its inverse recovers the functor. -/
@[simp] theorem comap_iso_hom_inv (F : SubgroupFunctor G) (e : H ≅ G) :
    (F.comap e.hom).comap e.inv = F := by
  rw [← comap_comp, e.inv_hom_id, comap_id]

/-- Pulling back along an inverse and then the original isomorphism recovers the functor. -/
@[simp] theorem comap_iso_inv_hom (F : SubgroupFunctor H) (e : H ≅ G) :
    (F.comap e.inv).comap e.hom = F := by
  rw [← comap_comp, e.hom_inv_id, comap_id]

/-- Equality with an isomorphism preimage can be moved across the isomorphism. -/
theorem eq_comap_iso_iff {P : SubgroupFunctor H} {Q : SubgroupFunctor G} (e : H ≅ G) :
    P = Q.comap e.hom ↔ P.comap e.inv = Q := by
  constructor
  · rintro rfl
    exact comap_iso_hom_inv Q e
  · intro h
    have := congrArg (fun F : SubgroupFunctor G => F.comap e.hom) h
    simpa only [comap_iso_inv_hom] using this

/-- Isomorphism preimages reflect the all-test inclusion of subgroup functors. -/
theorem comap_iso_le_comap_iso_iff {P Q : SubgroupFunctor G} (e : H ≅ G) :
    P.comap e.hom ≤ Q.comap e.hom ↔ P ≤ Q := by
  constructor
  · intro h
    have := comap_mono (f := e.inv) h
    simpa only [comap_iso_hom_inv] using this
  · exact comap_mono

/-- Rational conjugacy in the same direction as the standard-parabolic classification:
`Int(g)` takes `P` onto `Q`, as an equality on every test scheme. -/
def IsRationallyConjugate (P Q : SubgroupFunctor G) : Prop :=
  ∃ g : Over.mk (𝟙 S) ⟶ G.X, P = Q.comap (G.innerIso g).hom

theorem IsRationallyConjugate.refl (P : SubgroupFunctor G) :
    P.IsRationallyConjugate P := by
  refine ⟨1, ?_⟩
  rw [innerIso_one_hom, comap_id]

theorem IsRationallyConjugate.symm {P Q : SubgroupFunctor G}
    (h : P.IsRationallyConjugate Q) : Q.IsRationallyConjugate P := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [innerIso_inv_hom]
  exact ((eq_comap_iso_iff (G.innerIso g)).mp hg).symm

theorem IsRationallyConjugate.trans {P Q R : SubgroupFunctor G}
    (hPQ : P.IsRationallyConjugate Q) (hQR : Q.IsRationallyConjugate R) :
    P.IsRationallyConjugate R := by
  obtain ⟨g, hg⟩ := hPQ
  obtain ⟨h, hh⟩ := hQR
  refine ⟨h * g, ?_⟩
  rw [innerIso_mul_hom, comap_comp, ← hh, ← hg]

/-- Rationally conjugate functors have exactly the same rational conjugacy predicates. -/
theorem IsRationallyConjugate.conjugate_iff {P Q : SubgroupFunctor G}
    (hPQ : P.IsRationallyConjugate Q) (R : SubgroupFunctor G) :
    P.IsRationallyConjugate R ↔ Q.IsRationallyConjugate R :=
  ⟨fun h => hPQ.symm.trans h, fun h => hPQ.trans h⟩

/-- Transport existence and uniqueness of a conjugacy index along rational conjugacy. -/
theorem IsRationallyConjugate.existsUnique_index_iff {Index : Sort v}
    {P Q : SubgroupFunctor G} (hPQ : P.IsRationallyConjugate Q)
    (representative : Index → SubgroupFunctor G) :
    (∃! j, P.IsRationallyConjugate (representative j)) ↔
      ∃! j, Q.IsRationallyConjugate (representative j) := by
  simp_rw [hPQ.conjugate_iff]

end SubgroupFunctor

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Conjugating a cocharacter gives a rationally conjugate dynamic parabolic. -/
theorem parabolic_isRationallyConjugate
    (zeta : (Gm S).toGrp ⟶ G) (g : Over.mk (𝟙 S) ⟶ G.X) :
    (parabolic zeta).IsRationallyConjugate
      (parabolic (zeta ≫ (G.innerIso g).hom)) :=
  ⟨g, parabolic_eq_comap_of_iso zeta (G.innerIso g)⟩

end Dynamic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The exact unique-standard-index assertion is unchanged by rational conjugacy
of the dynamic parabolic. No structural classification assertion is assumed or proved. -/
theorem standardParabolic_unique_conjugacy_index_iff [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {P Q : SubgroupFunctor G} (hPQ : P.IsRationallyConjugate Q) :
    (∃! J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        P = (standardParabolic i ν J.1).comap (G.innerIso g).hom) ↔
    ∃! J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        Q = (standardParabolic i ν J.1).comap (G.innerIso g).hom := by
  simpa only [SubgroupFunctor.IsRationallyConjugate] using
    (hPQ.existsUnique_index_iff
      (fun J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν} =>
        standardParabolic i ν J.1))

/-- Conjugating an arbitrary cocharacter preserves the exact unique-standard-index
assertion on all test schemes, including the direction of its `comap`. -/
theorem standardParabolic_unique_conjugacy_index_comp_innerIso_iff
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (∃! J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      ∃ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        Dynamic.parabolic zeta =
          (standardParabolic i ν J.1).comap (G.innerIso h).hom) ↔
    ∃! J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      ∃ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        Dynamic.parabolic (zeta ≫ (G.innerIso g).hom) =
          (standardParabolic i ν J.1).comap (G.innerIso h).hom :=
  standardParabolic_unique_conjugacy_index_iff i ν
    (Dynamic.parabolic_isRationallyConjugate zeta g)

end Langlands.GroupScheme
