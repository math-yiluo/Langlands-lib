import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-! # A common Galois overfield of a finite family of number fields -/

noncomputable section

namespace Langlands.ClassField.Global

universe u w

variable (E : Type u) [Field E] {ι : Type w} (L : ι → Type u) [∀ i, Field (L i)]
  [∀ i, Algebra E (L i)]

/-- A number field, Galois over `E`, together with an embedding over `E` of every member
of the family `L`. The algebra structures and scalar towers record these embeddings. -/
structure FamilyGaloisOverfield where
  carrier : Type u
  [field : Field carrier]
  [numberField : NumberField carrier]
  [algebraBase : Algebra E carrier]
  [algebraMember : ∀ i, Algebra (L i) carrier]
  [tower : ∀ i, IsScalarTower E (L i) carrier]
  [galois : IsGalois E carrier]

attribute [instance] FamilyGaloisOverfield.field FamilyGaloisOverfield.numberField
  FamilyGaloisOverfield.algebraBase FamilyGaloisOverfield.algebraMember
  FamilyGaloisOverfield.tower FamilyGaloisOverfield.galois

variable [NumberField E] [∀ i, NumberField (L i)] [Finite ι]

/-- Embed every member of a finite family over `E` in the algebraic closure of `E` and
take the supremum of their normal closures. This stays in the universe of `E`. -/
def familyGaloisOverfield : FamilyGaloisOverfield E L := by
  let Ω := AlgebraicClosure E
  let f : ∀ i, L i →ₐ[E] Ω := fun _ => IsAlgClosed.lift
  let N : ι → IntermediateField E Ω := fun i => IntermediateField.normalClosure E (L i) Ω
  let M : IntermediateField E Ω := ⨆ i, N i
  letI : FiniteDimensional E M := IntermediateField.finiteDimensional_iSup_of_finite
  letI : Normal E M := IntermediateField.normal_iSup E Ω N
  letI : NumberField M := NumberField.of_module_finite E M
  letI : IsGalois E M := ⟨⟩
  let j : ∀ i, L i →ₐ[E] M := fun i => (f i).codRestrict M.toSubalgebra fun x =>
    (le_iSup N i : N i ≤ M) ((f i).fieldRange_le_normalClosure ⟨x, rfl⟩)
  letI : ∀ i, Algebra (L i) M := fun i => (j i).toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower E (L i) M := fun i => IsScalarTower.of_algHom (j i)
  exact { carrier := M }

end Langlands.ClassField.Global
