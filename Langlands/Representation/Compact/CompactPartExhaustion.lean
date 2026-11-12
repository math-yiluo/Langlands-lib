import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.CompactCoefficient.ProjectiveLifting
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! # Exhaustion when every irreducible subquotient has compact coefficients -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open CategoryTheory CompactCoefficientClass SmoothRep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Compact irreducible constituents exhaust the object through their actual isotypic images. -/
theorem totalIsotypic_eq_top_of_compact_irreducible_subquotients
    (A : SmoothRep.{0, u, v} ℂ G)
    (hA : ∀ D : SmoothRep.{0, u, v} ℂ G, D.IsIrreducible → IsSubquotient D A →
      HasCompactSmoothDualCoefficients D.representation) :
    totalIsotypicSubrepresentation.{u, v} A = ⊤ := by
  classical
  let T := totalIsotypicSubrepresentation.{u, v} A
  by_contra hT
  obtain ⟨x, hx⟩ : ∃ x : A, x ∉ T := by
    by_contra hn
    push Not at hn
    exact hT (eq_top_iff.mpr fun y _ => hn y)
  let Q := quotient A T
  let xQ : Q := hom (mkQ A T) x
  have hxQ : xQ ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero T.toSubmodule).mp h)
  let : Nontrivial Q := ⟨⟨xQ, 0, hxQ⟩⟩
  obtain ⟨D, hD, hDQ⟩ := exists_isIrreducible_isSubquotient_of_nontrivial Q
  have hQA : IsSubquotient Q A :=
    isSubquotient_iff_exists.mpr ⟨A, 𝟙 A, mkQ A T, Function.injective_id, mkQ_surjective A T⟩
  have hc := hA D hD (Langlands.smoothSubquotientTransitivity ℂ G A Q D hDQ hQA)
  let : Projective D := CompactCoefficient.projective_of_hasCompactSmoothDualCoefficients D hD hc
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDQ
  let : Epi q := (epi_iff_surjective q).mpr hq
  let s : D ⟶ C := Projective.factorThru (𝟙 D) q
  have hs : s ≫ q = 𝟙 D := Projective.factorThru_comp (𝟙 D) q
  let f : D ⟶ Q := s ≫ i
  have hf : Function.Injective (hom f) := by
    intro a b hab
    have hsab : hom s a = hom s b := hi hab
    have heqa := congrArg (fun t => hom t a) hs
    have heqb := congrArg (fun t => hom t b) hs
    exact heqa.symm.trans ((congrArg (hom q) hsab).trans heqb)
  let : Epi (mkQ A T) := (SmoothRep.epi_iff_surjective (mkQ A T)).mpr (mkQ_surjective A T)
  let t : D ⟶ A := Projective.factorThru f (mkQ A T)
  have ht : t ≫ mkQ A T = f := Projective.factorThru_comp f (mkQ A T)
  let R : IrreducibleCompactCoefficientRep.{u, v} G := ⟨D, hD, hc⟩
  have hrange : (hom t).range ≤ T :=
    (range_le_isotypicSubrepresentation R rfl (hom t)).trans
      (isotypicSubrepresentation_le_totalIsotypicSubrepresentation A (ofRep R))
  let : D.representation.IsIrreducible := hD
  let : Nontrivial D := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) D.representation.asModule
  obtain ⟨y, hy⟩ := exists_ne (0 : D)
  have hty : hom t y ∈ T := hrange ⟨y, rfl⟩
  have hqzero : hom (mkQ A T) (hom t y) = 0 :=
    (Submodule.Quotient.mk_eq_zero T.toSubmodule).mpr hty
  have hfy : hom f y = 0 :=
    (congrArg (fun z => hom z y) ht).symm.trans hqzero
  exact hy (hf (hfy.trans (map_zero (hom f)).symm))

/-- In particular, all-compact irreducible subquotients force compact coefficients of the object. -/
theorem compactCoefficients_of_compact_irreducible_subquotients
    (A : SmoothRep.{0, u, v} ℂ G)
    (hA : ∀ D : SmoothRep.{0, u, v} ℂ G, D.IsIrreducible → IsSubquotient D A →
      HasCompactSmoothDualCoefficients D.representation) :
    HasCompactSmoothDualCoefficients A.representation := by
  intro x
  apply totalIsotypicSubrepresentation_le_compactCoefficientVectors A
  rw [totalIsotypic_eq_top_of_compact_irreducible_subquotients A hA]
  trivial

end Langlands.Renard.CompactRepresentation
