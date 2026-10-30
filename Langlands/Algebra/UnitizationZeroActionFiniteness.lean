import Langlands.Algebra.UnitizationZeroActionFinitenessStatements
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.LinearAlgebra.Countable
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Proof of the zero-action separation of unitized finiteness conventions

Proves `ZeroActionFinitenessStatements` from
`Langlands.Algebra.UnitizationZeroActionFinitenessStatements`: with the zero original action on
the complex line, the complex unitization acts finitely and Noetherianly, while the integer
unitization acts neither finitely nor Noetherianly.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationZeroActionFiniteness

universe uA

/-- The positive branch: the complex line is finite and Noetherian over itself, and the named
scalar tower `CompatibleUnitization.isScalarTower` transfers both properties to the actual
complex-unitized zero action. -/
theorem complexZeroAction : ComplexZeroActionStatement.{uA} := fun A _ _ _ _ =>
  letI := CompatibleUnitization.module (0 : A →ₙₐ[ℂ] Module.End ℂ ℂ)
  haveI : IsScalarTower ℂ (Unitization ℂ A) ℂ :=
    CompatibleUnitization.isScalarTower (0 : A →ₙₐ[ℂ] Module.End ℂ ℂ)
  haveI : IsPrincipalIdealRing ℂ := DivisionSemiring.isPrincipalIdealRing ℂ
  ⟨Module.Finite.of_restrictScalars_finite ℂ (Unitization ℂ A) ℂ (hM := Module.Finite.self ℂ),
    isNoetherian_of_tower ℂ (PrincipalIdealRing.isNoetherianRing (R := ℂ))⟩

/-- The negative branch: the identity of `ℂ` is semilinear along the first coordinate
`Unitization.fstHom ℤ A` for the actual integer-unitized zero action, so finiteness over the
integer unitization would give finiteness over `ℤ`, hence countability of `ℂ`. Noetherianity
would imply the same finiteness. -/
theorem integerZeroAction : IntegerZeroActionStatement.{uA} := fun A _ =>
  letI := CompatibleUnitization.module (0 : A →ₙₐ[ℤ] Module.End ℤ ℂ)
  have hfin : ¬ Module.Finite (Unitization ℤ A) ℂ := fun _ => by
    let f : ℂ →ₛₗ[(Unitization.fstHom ℤ A).toRingHom] ℂ :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun x z => CompatibleUnitization.zero_smul_eq x z }
    have : Module.Finite ℤ ℂ := Module.Finite.of_surjective f Function.surjective_id
    exact not_countable_complex
      (Set.countable_univ_iff.mpr (Finsupp.Countable.of_moduleFinite (R := ℤ)))
  ⟨hfin, fun _ => hfin (Module.IsNoetherian.finite (Unitization ℤ A) ℂ)⟩

/-- The positive complex and negative integer zero-action targets, in order. -/
theorem zeroActionFiniteness : ZeroActionFinitenessStatements.{uA} :=
  ⟨complexZeroAction, integerZeroAction⟩

end Langlands.Algebra.UnitizationZeroActionFiniteness
