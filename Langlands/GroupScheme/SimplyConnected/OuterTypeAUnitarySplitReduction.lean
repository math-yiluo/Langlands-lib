import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitPresentationStatement
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleStatement
import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianCocycle
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsMixedDiscrepancy
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsScalarTrivial
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianDescent
import Langlands.GroupScheme.Examples.HermitianMatrixPresentationFromPoints
import Langlands.LinearAlgebra.UnitaryTwistedDescent

/-! # Outer type A presentations from the Tits cocycle and unitary splitting -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OuterTypeAUnitarySplit

open SpecialLinearTitsCocycle Matrix
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose

section Discrepancy

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- The matrix form of the inner discrepancy formula, as in clause 1 of
`SpecialLinearTitsCocycleStatement`: on every test `Z` and cover point `a`, the discrepancy of
`σ` sends `g` to `X g X⁻¹`, where `X` is the coefficient image of `X` under `a`. -/
def IsInnerMatrixFormula (σ : M ≃ₐ[K] M) (X : GeneralLinearGroup (Fin (n + 1)) M) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
    (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      (GeneralLinearGroup.map (coefficients a) X :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
        (GeneralLinearGroup.map (coefficients a) X⁻¹ :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))

/-- The matrix form of the outer discrepancy formula, as in clause 1 of
`SpecialLinearTitsCocycleStatement`: on every test `Z` and cover point `a`, the discrepancy of
`σ` sends `g` to `X (g⁻¹)ᵀ X⁻¹`, where `X` is the coefficient image of `X` under `a`. -/
def IsOuterMatrixFormula (σ : M ≃ₐ[K] M) (X : GeneralLinearGroup (Fin (n + 1)) M) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
    (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      (GeneralLinearGroup.map (coefficients a) X :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
        ((g⁻¹ : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
        (GeneralLinearGroup.map (coefficients a) X⁻¹ :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))

/-- The matrix form of an inner discrepancy formula gives an inner representative. -/
theorem hasInnerDiscrepancy_of_matrix {σ : M ≃ₐ[K] M}
    {X : GeneralLinearGroup (Fin (n + 1)) M} (h : IsInnerMatrixFormula E σ X) :
    HasInnerDiscrepancy E σ X := by
  intro Z a g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv]
  exact h Z a g

/-- The matrix form of an outer discrepancy formula gives an outer representative. -/
theorem hasOuterDiscrepancy_of_matrix {σ : M ≃ₐ[K] M}
    {X : GeneralLinearGroup (Fin (n + 1)) M} (h : IsOuterMatrixFormula E σ X) :
    HasOuterDiscrepancy E σ X := by
  intro Z a g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv]
  exact h Z a g

/-- An outer representative gives the matrix form of the outer discrepancy formula. -/
theorem isOuterMatrixFormula_of_hasOuterDiscrepancy {σ : M ≃ₐ[K] M}
    {X : GeneralLinearGroup (Fin (n + 1)) M} (hX : HasOuterDiscrepancy E σ X) :
    IsOuterMatrixFormula E σ X := by
  intro Z a g
  have h := congrArg Units.val (hX Z a g)
  rw [Units.val_mul, Units.val_mul, ← map_inv] at h
  exact h

end Discrepancy

/-- The Tits cocycle presentation of type-A groups implies that, over a field where every
central simple algebra with a unitary involution splits, every outer form of type A has an
all-test presentation as the special unitary group of a Hermitian matrix. -/
theorem outerTypeAUnitarySplitPresentation_of_specialLinearTitsCocycle
    (hcoc : SpecialLinearTitsCocycleStatement.{u}) :
    OuterTypeAUnitarySplitPresentationStatement.{u} := by
  classical
  intro K _ hK G _ _ d n hsc has ⟨e, hA⟩ ⟨σ₀, v₀, hmove⟩
  have hnot : ¬ d.StarIsTrivial := fun h => hmove (h σ₀ v₀)
  have hstar := d.starImagePair_of_A e hA hnot
  have hn : 2 ≤ n := hstar.two_le
  have := hstar.isQuadraticExtension
  have := hstar.isGalois
  obtain ⟨M, _, _, _, _, ι₀, E, x, χ, hcoc1, -, -⟩ := hcoc K G d n e hsc has hA
  have hshape : HasStarDiscrepancy E d ι₀ x := fun σ τ hτ =>
    ⟨fun h => hasInnerDiscrepancy_of_matrix E fun Z a g => (hcoc1 σ τ hτ Z a g).1 h,
      fun h => hasOuterDiscrepancy_of_matrix E fun Z a g => (hcoc1 σ τ hτ Z a g).2 h⟩
  have hle := hshape.starField_le_cover E d hn
  let f := starFieldToCover d ι₀ hle
  let F : IntermediateField K M := f.fieldRange
  let H := F.fixingSubgroup
  have : Algebra.IsQuadraticExtension K F :=
    ⟨(f.equivFieldRange.toLinearEquiv.finrank_eq).symm.trans hstar.finrank_starField⟩
  have hfix (σ : M ≃ₐ[K] M) : σ ∈ H ↔ ∀ z : d.starField, σ (f z) = f z := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h z
      exact h (f z) ⟨z, rfl⟩
    · rintro h y ⟨z, rfl⟩
      exact h z
  have hI : ∀ σ ∈ H, HasInnerDiscrepancy E σ (x σ) := fun σ hσ =>
    hshape.inner_of_fixes_starField d ι₀ hle E σ ((hfix σ).mp hσ)
  have hO : ∀ σ ∉ H, HasOuterDiscrepancy E σ (x σ) := by
    intro σ hσ
    apply hshape.outer_of_not_fixes_starField d ι₀ hle E σ
    by_contra! h
    exact hσ ((hfix σ).mpr h)
  have hH : H.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  have hcyc := isTwistedProjectiveCocycle_of_discrepancy E hH hI hO
  obtain ⟨P, hP⟩ :=
    Langlands.LinearAlgebra.UnitaryTwistedDescent.exists_conj_eq_scalar hK F hcyc.1 hcyc.2
  have htriv : HasTrivialDiscrepancy (coordinateChange E P) H :=
    hasTrivialDiscrepancy_coordinateChange_of_scalar E hI P hP
  obtain ⟨σ, hσ⟩ := exists_starFieldToCover_conjugation d e hstar ι₀ hle
  have hnontrivial :
      ∃ z : d.starField, (SU3Root.fieldInvolution K d.starField).bar z ≠ z := by
    by_contra! h
    apply SU3Root.conjugation_ne_one K d.starField
    exact AlgEquiv.ext h
  have hmoves : ∃ z : d.starField, σ (f z) ≠ f z := by
    obtain ⟨z, hz⟩ := hnontrivial
    refine ⟨z, ?_⟩
    rw [hσ]
    exact fun h => hz (f.injective h)
  have houter :=
    (hshape.outer_of_not_fixes_starField d ι₀ hle E σ hmoves).coordinateChange E P
  obtain ⟨J, hJ⟩ := exists_hermitian_outer_representative (coordinateChange E P) f
    (SU3Root.fieldInvolution K d.starField) hnontrivial htriv σ hσ _ houter
  let _ : Algebra d.starField M := f.toRingHom.toAlgebra
  have : IsScalarTower K d.starField M := IsScalarTower.of_algebraMap_eq fun r =>
    (f.commutes r).symm
  have hin : OuterTypeAHermitian.InnerTrivial d.starField (coordinateChange E P) := by
    intro τ hτ Z a g
    exact htriv ⟨τ, (hfix τ).mpr hτ⟩ Z a g
  have hout : OuterTypeAHermitian.OuterHermitian d.starField J (coordinateChange E P) := by
    intro τ hτ Z a g
    exact isOuterMatrixFormula_of_hasOuterDiscrepancy (coordinateChange E P)
      (hJ τ (starFieldToCover_conjugation_of_not_fixed d e hstar ι₀ hle τ hτ)) Z a g
  let φ := OuterTypeAHermitian.descendedIso d.starField J (coordinateChange E P) hin hout
  refine ⟨d.starField, inferInstance, inferInstance, inferInstance, inferInstance, J, ⟨?_⟩⟩
  exact HermitianMatrix.SchemeModel.Presentation.ofMatrixPoints K d.starField J G
    (OuterTypeAHermitian.matrixPoints K d.starField J φ)
    (OuterTypeAHermitian.matrixPoints_injective K d.starField J φ)
    (fun T g => OuterTypeAHermitian.mem_range_matrixPoints K d.starField J φ T g)
    (fun a y => OuterTypeAHermitian.matrixPoints_naturality K d.starField J φ a y)

end Langlands.GroupScheme.OuterTypeAUnitarySplit
