import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Internal Noetherian core for endomorphism localization

Derived statement targets motivated by Renard 2026, Appendix C.II,
printed page 279 / PDF page 285. These concern ordinary unital modules and
actual linear maps; the construction and hypotheses of the source's actual
localization remain separate obligations.
-/

set_option autoImplicit false

namespace Langlands.LinearAlgebra.NoetherianLocalizationCore

universe uR uM uN

/-- An invariant submodule of a Noetherian module is also inverse-invariant
under an actual linear automorphism. -/
def InversePreservesSubmoduleStatement : Prop :=
  ∀ (R : Type uR) (M : Type uM)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (e : M ≃ₗ[R] M) (P : Submodule R M),
    (∀ x ∈ P, e x ∈ P) →
      ∀ x ∈ P, e.symm x ∈ P

/-- Power exhaustion of a Noetherian target by the range of an intertwining
linear map implies surjectivity. -/
def ExhaustionSurjectiveStatement : Prop :=
  ∀ (R : Type uR) (M : Type uM) (N : Type uN)
    [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsNoetherian R N]
    (a : Module.End R M) (e : N ≃ₗ[R] N) (f : M →ₗ[R] N),
    (∀ x : M, f (a x) = e (f x)) →
    (∀ y : N, ∃ (n : ℕ) (x : M), (e ^ n) y = f x) →
      Function.Surjective f

/-- With a Noetherian source and locally nilpotent kernel as well, a
positive source power has the same kernel as the map and is stable. -/
def StablePowerStatement : Prop :=
  ∀ (R : Type uR) (M : Type uM) (N : Type uN)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherian R M]
    [AddCommGroup N] [Module R N] [IsNoetherian R N]
    (a : Module.End R M) (e : N ≃ₗ[R] N) (f : M →ₗ[R] N),
    (∀ x : M, f (a x) = e (f x)) →
    (∀ y : N, ∃ (n : ℕ) (x : M), (e ^ n) y = f x) →
    (∀ x : M, f x = 0 → ∃ n : ℕ, (a ^ n) x = 0) →
      Function.Surjective f ∧
        ∃ n : ℕ, 0 < n ∧
          LinearMap.ker f = LinearMap.ker (a ^ n) ∧
          LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) ∧
          LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)

/-- The three internal Noetherian localization-core targets. -/
def NoetherianLocalizationCoreStatement : Prop :=
  InversePreservesSubmoduleStatement.{uR, uM} ∧
    ExhaustionSurjectiveStatement.{uR, uM, uN} ∧
    StablePowerStatement.{uR, uM, uN}

end Langlands.LinearAlgebra.NoetherianLocalizationCore
