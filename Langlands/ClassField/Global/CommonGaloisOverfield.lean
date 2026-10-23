import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-! # Common Galois overfields of number-field towers -/

noncomputable section

namespace Langlands.ClassField.Global

universe u

variable (F E L₁ L₂ : Type u) [Field F] [Field E] [Field L₁] [Field L₂]
  [Algebra F E] [Algebra F L₁] [Algebra F L₂] [Algebra E L₁] [Algebra E L₂]
  [IsScalarTower F E L₁] [IsScalarTower F E L₂]

/-- A common number-field overfield of two towers, Galois over their common base.
The algebra structures specify embeddings agreeing on the shared field `E`. -/
structure CommonGaloisOverfield where
  carrier : Type u
  [field : Field carrier]
  [numberField : NumberField carrier]
  [algebraF : Algebra F carrier]
  [algebraE : Algebra E carrier]
  [algebraLeft : Algebra L₁ carrier]
  [algebraRight : Algebra L₂ carrier]
  [towerFE : IsScalarTower F E carrier]
  [towerFLeft : IsScalarTower F L₁ carrier]
  [towerFRight : IsScalarTower F L₂ carrier]
  [towerELeft : IsScalarTower E L₁ carrier]
  [towerERight : IsScalarTower E L₂ carrier]
  [galois : IsGalois F carrier]

attribute [instance] CommonGaloisOverfield.field CommonGaloisOverfield.numberField
  CommonGaloisOverfield.algebraF CommonGaloisOverfield.algebraE
  CommonGaloisOverfield.algebraLeft CommonGaloisOverfield.algebraRight
  CommonGaloisOverfield.towerFE CommonGaloisOverfield.towerFLeft
  CommonGaloisOverfield.towerFRight CommonGaloisOverfield.towerELeft
  CommonGaloisOverfield.towerERight CommonGaloisOverfield.galois

variable [NumberField F] [NumberField E] [NumberField L₁] [NumberField L₂]
  [IsGalois F L₁] [IsGalois F L₂]

/-- Embed both extensions over `E` in its algebraic closure and take the compositum
of their ranges over `F`. This stays in the original universe. -/
def commonGaloisOverfield : CommonGaloisOverfield F E L₁ L₂ := by
  let Ω := AlgebraicClosure E
  let f₁ : L₁ →ₐ[E] Ω := IsAlgClosed.lift
  let f₂ : L₂ →ₐ[E] Ω := IsAlgClosed.lift
  let g₁ := f₁.restrictScalars F
  let g₂ := f₂.restrictScalars F
  let M : IntermediateField F Ω := g₁.fieldRange ⊔ g₂.fieldRange
  letI : FiniteDimensional F g₁.fieldRange := g₁.equivFieldRange.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional F g₂.fieldRange := g₂.equivFieldRange.toLinearEquiv.finiteDimensional
  letI : Normal F g₁.fieldRange := Normal.of_algEquiv g₁.equivFieldRange
  letI : Normal F g₂.fieldRange := Normal.of_algEquiv g₂.equivFieldRange
  letI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  letI : Normal F M := IntermediateField.normal_sup F Ω _ _
  letI : NumberField M := NumberField.of_module_finite F M
  letI : IsGalois F M := ⟨⟩
  let j₁ : L₁ →ₐ[F] M := g₁.codRestrict M.toSubalgebra fun x =>
    (le_sup_left : g₁.fieldRange ≤ M) ⟨x, rfl⟩
  let j₂ : L₂ →ₐ[F] M := g₂.codRestrict M.toSubalgebra fun x =>
    (le_sup_right : g₂.fieldRange ≤ M) ⟨x, rfl⟩
  let j : E →ₐ[F] M := j₁.comp (IsScalarTower.toAlgHom F E L₁)
  letI : Algebra E M := j.toRingHom.toAlgebra
  letI : Algebra L₁ M := j₁.toRingHom.toAlgebra
  letI : Algebra L₂ M := j₂.toRingHom.toAlgebra
  letI : IsScalarTower F E M := IsScalarTower.of_algHom j
  letI : IsScalarTower F L₁ M := IsScalarTower.of_algHom j₁
  letI : IsScalarTower F L₂ M := IsScalarTower.of_algHom j₂
  letI : IsScalarTower E L₁ M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower E L₂ M := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change f₁ (algebraMap E L₁ x) = f₂ (algebraMap E L₂ x)
    rw [f₁.commutes, f₂.commutes]
  exact { carrier := M }

end Langlands.ClassField.Global
