import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # A common extension of a finite family of finite field extensions -/

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

variable (K : Type u) [Field K] {ι : Type v} (L : ι → Type u)
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, FiniteDimensional K (L i)]

private def intoAlgebraicClosure (i : ι) : L i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift

/-- The compositum of chosen images of a family of finite extensions inside
one algebraic closure of the base. -/
def commonFiniteExtension : IntermediateField K (AlgebraicClosure K) :=
  ⨆ i, (intoAlgebraicClosure K L i).fieldRange

/-- Each member of the family embeds into the compositum over the base. -/
def commonFiniteExtensionEmb (i : ι) : L i →ₐ[K] commonFiniteExtension K L :=
  (intoAlgebraicClosure K L i).codRestrict _ fun x =>
    (le_iSup (fun j => (intoAlgebraicClosure K L j).fieldRange) i) ⟨x, rfl⟩

/-- The compositum is finite over the base when the family is finite. -/
theorem finiteDimensional_commonFiniteExtension [Finite ι] :
    FiniteDimensional K (commonFiniteExtension K L) := by
  have (i : ι) : FiniteDimensional K ((intoAlgebraicClosure K L i).fieldRange) :=
    Module.Finite.equiv (AlgEquiv.ofInjectiveField (intoAlgebraicClosure K L i)).toLinearEquiv
  exact IntermediateField.finiteDimensional_iSup_of_finite

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
