import Langlands.Algebra.IntegerNonUnitalSubmodule
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Noetherian criteria for the original nonunital action

Closed internal targets comparing the actual integer-unitized module with
the original stable additive subgroups. No comparison is proved here.
-/

set_option autoImplicit false

namespace Langlands.Algebra.IntegerOriginalSubmoduleNoetherian

universe uA uM

/-- Ordinary Noetherianity of the canonical integer-unitized module is ACC
on the original stable additive subgroups. -/
def ACCStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M],
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
     IsNoetherian (Unitization ℤ A) M) ↔
    WellFoundedGT (NonUnitalSubmodule A M)

/-- Every nonempty subset of the original stable additive subgroups has
a member maximal for proper inclusion exactly when the actual
integer-unitized module is Noetherian. -/
def MaximalStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M],
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
     IsNoetherian (Unitization ℤ A) M) ↔
    ∀ s : Set (NonUnitalSubmodule A M), s.Nonempty →
      ∃ S ∈ s, ∀ T ∈ s, ¬ S < T

/-- Every increasing natural-indexed chain of original stable additive
subgroups is eventually constant exactly when the actual
integer-unitized module is Noetherian. -/
def ChainStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M],
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
     IsNoetherian (Unitization ℤ A) M) ↔
    ∀ c : ℕ →o NonUnitalSubmodule A M,
      ∃ n, ∀ m, n ≤ m → c n = c m

/-- The ACC, maximal-element and increasing-sequence criteria, in that order. -/
def IntegerOriginalSubmoduleNoetherianStatement : Prop :=
  ACCStatement.{uA, uM} ∧ MaximalStatement.{uA, uM} ∧
    ChainStatement.{uA, uM}

end Langlands.Algebra.IntegerOriginalSubmoduleNoetherian
