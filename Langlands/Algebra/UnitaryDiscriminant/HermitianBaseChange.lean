import Langlands.Algebra.UnitaryDiscriminant.BaseChange
import Langlands.Algebra.UnitaryDiscriminant.HermitianMatrix
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof

/-! # Norm criterion after a Hermitian scalar extension -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open BrauerComparison ClassFieldTheory.Local ClassFieldTheory.Local.CyclicClassAlgebra
open LocalClassField

private theorem centerCharacter_eq_restrict {F L M : Type u} [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    [Algebra.IsQuadraticExtension F L] [Normal F L]
    {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) :
    centerCharacter (M := M) hι = (centerCharacter (M := L) hι).comp (AlgEquiv.restrictNormalHom L) := by
  apply MonoidHom.ext
  intro g
  apply Multiplicative.toAdd.injective
  rw [MonoidHom.comp_apply, centerCharacter_toAdd, centerCharacter_toAdd]
  have h : g ∈ centerFixing F L M ↔ (AlgEquiv.restrictNormalHom L) g ∈ centerFixing F L L := by
    rw [mem_centerFixing, mem_centerFixing]
    constructor
    · intro hg x
      apply (algebraMap L M).injective
      exact (g.restrictNormal_commutes L x).trans (hg x)
    · intro hg x
      exact (g.restrictNormal_commutes L x).symm.trans (congrArg (algebraMap L M) (hg x))
  by_cases hg : g ∈ centerFixing F L M
  · rw [ite_eq_left hg, ite_eq_left (h.mp hg)]
  · rw [ite_eq_right hg, ite_eq_right (hg ∘ h.mpr)]

variable {F L M F' L' : Type u} [Field F] [Field L] [Field M] [Field F'] [Field L']
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [Algebra F F'] [Algebra F' L'] [Algebra L L'] [Algebra F L']
  [IsScalarTower F F' L'] [IsScalarTower F L L']
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension F' L']
  [FiniteDimensional F M] [IsGalois F M] [IsGalois F' L'] [CharZero F']
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {ι' : L' ≃ₐ[F'] L'} (hι' : ι' ≠ 1)
  (hιcompat : ∀ x : L, ι' (algebraMap L L' x) = algebraMap L L' (ι x))
  {A : CSA.{u, u} L} {m : ℕ} {τ : A → A} (hτ : IsUnitaryInvolution ι τ)
  {τ' : L' ⊗[L] A → L' ⊗[L] A} (hτ' : IsUnitaryInvolution ι' τ')
  (hτcompat : ∀ a : A, τ' (1 ⊗ₜ[L] a) = 1 ⊗ₜ[L] τ a)
  (e : M ⊗[L] A ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M)
  (f : L' ⊗[L] A ≃ₐ[L'] Matrix (Fin (2 * m)) (Fin (2 * m)) L')
  (H : GL (Fin (2 * m)) L')
  (hHerm : ((H : Matrix (Fin (2 * m)) (Fin (2 * m)) L').map ι')ᵀ = H)
  (hf : ∀ b, f (τ' b) = ((H⁻¹ : GL (Fin (2 * m)) L') : Matrix _ _ L') *
    ((f b).map ι')ᵀ * (H : Matrix _ _ L'))
  (d : F'ˣ) (hd : algebraMap F' L' (d : F') =
    (-1 : L')^m * (GeneralLinearGroup.det H : L'))

include hι' hιcompat hτ' hτcompat hHerm hf hd in
/-- After a Hermitian scalar extension, the discriminant vanishes exactly when the
signed determinant is a norm from the quadratic field center. -/
theorem scalarExtension_discriminantClass_eq_zero_iff_norm :
    Brauer.scalarExtension F' (discriminantClass hι hτ e) = 0 ↔ d ∈ normSubgroup F' L' := by
  classical
  let S := AlgebraicClosure F'
  let jL' : L' →ₐ[F'] S := IsAlgClosed.lift
  let : Algebra L' S := jL'.toRingHom.toAlgebra
  let : IsScalarTower F' L' S := IsScalarTower.of_algHom jL'
  let : Algebra L S := Algebra.compHom S (algebraMap L L')
  let : IsScalarTower L L' S := IsScalarTower.of_algebraMap_eq' rfl
  have hbase (x : F) : algebraMap L S (algebraMap F L x) = algebraMap F S x := by
    rw [IsScalarTower.algebraMap_apply L L' S, ← IsScalarTower.algebraMap_apply F L L',
      IsScalarTower.algebraMap_apply F F' L', ← IsScalarTower.algebraMap_apply F' L' S,
      ← IsScalarTower.algebraMap_apply F F' S]
  let : IsScalarTower F L S := IsScalarTower.of_algebraMap_eq fun x => (hbase x).symm
  let : FiniteDimensional L M := FiniteDimensional.right F L M
  let jM : M →ₐ[L] S := IsAlgClosed.lift
  obtain ⟨U, iM, hiM⟩ := exists_finiteStage_containing (E := F') (jM.restrictScalars F)
  obtain ⟨V, iL', hiL'⟩ := exists_finiteStage_containing (E := F') jL'
  let W := U ⊔ V
  let iUW : U →ₐ[F'] W := IntermediateField.inclusion le_sup_left
  let aM : M →ₐ[F] W := (iUW.restrictScalars F).comp iM
  let aL' : L' →ₐ[F'] W :=
    (IntermediateField.inclusion (show V.toIntermediateField ≤ W.toIntermediateField from le_sup_right)).comp iL'
  let : Algebra M W := aM.toRingHom.toAlgebra
  let : Algebra L' W := aL'.toRingHom.toAlgebra
  let : IsScalarTower F M W := IsScalarTower.of_algHom aM
  let : IsScalarTower F' L' W := IsScalarTower.of_algHom aL'
  let : Algebra L W := Algebra.compHom W (algebraMap L L')
  let : IsScalarTower L L' W := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L M W := IsScalarTower.of_algebraMap_eq fun x => by
    apply W.toIntermediateField.val.injective
    change (iL' (algebraMap L L' x) : S) = (iM (algebraMap L M x) : S)
    rw [hiL', hiM]
    exact (jM.commutes x).symm
  let e' := baseChangeSplittingChart (A := A) L' (↑W) e
  rw [scalarExtension_discriminantClass_baseChange (M' := W) hι hι' hιcompat hτ hτ' hτcompat e]
  let b := discriminantClass hι' hτ' e'
  change b = 0 ↔ _
  have hBrauer : (b = 0) ↔ relativeDiscriminantClass hι' hτ' e' = 0 := by
    rw [← (brauerContinuousEquiv F' S).injective.eq_iff, map_zero,
      brauerContinuousEquiv_discriminantClass, ← map_zero (relativeToContinuous F' W S 2)]
    exact (relativeToContinuous_injective F' S W).eq_iff
  rw [hBrauer, relativeDiscriminantClass_of_hermitian hι' hτ' e' f H hHerm hf d hd,
    centerCharacter_eq_restrict hι', ← relativeInflation_cyclicClass,
    ← map_zero (relativeInflation F' L' W 2).hom,
    (finiteRelativeH2InflationExactness F' L' W).1.eq_iff,
    cyclicClass_eq_zero_iff_of_injective _ (centerCharacter_injective hι'), inv_mem_iff]

end Langlands.UnitaryDiscriminant
