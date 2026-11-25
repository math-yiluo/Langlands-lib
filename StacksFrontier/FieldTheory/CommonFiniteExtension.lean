module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# A common finite extension for a finite family of finite extensions

A finite family of finite field extensions of `K` admits a single finite extension of `K` into
which every member embeds over `K`: take the compositum, inside an algebraic closure of `K`, of
the images of the members under liftings to that closure. If every member of the family is
moreover separable over `K`, so is that compositum, each image being separable and a supremum of
separable subextensions being separable.

We also record that adjoining finitely many algebraic elements to `K` gives a finite extension
(`IntermediateField.finiteDimensional_adjoin_range_of_isAlgebraic`).
-/

public noncomputable section

universe u v

/-- Finitely many finite field extensions of `K` embed into a common finite extension of `K`. -/
theorem exists_finiteDimensional_algHom_forall {K : Type u} [Field K] {ι : Type v} [Finite ι]
    (F : ι → Type u) [∀ i, Field (F i)] [∀ i, Algebra K (F i)] [∀ i, Module.Finite K (F i)] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E),
      Nonempty (∀ i, F i →ₐ[K] E) := by
  let f (i : ι) : F i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let T : IntermediateField K (AlgebraicClosure K) := ⨆ i, (f i).fieldRange
  have (i : ι) : Module.Finite K (f i).fieldRange :=
    Module.Finite.equiv (f i).equivFieldRange.toLinearEquiv
  have : Module.Finite K T := IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨T, inferInstance, inferInstance, inferInstance, ⟨fun i => ?_⟩⟩
  exact (IntermediateField.inclusion (le_iSup (fun i => (f i).fieldRange) i)).comp
    (f i).equivFieldRange.toAlgHom
