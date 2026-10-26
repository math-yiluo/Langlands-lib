import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Basic.Complex.Basic
import Mathlib.Order.Disjoint

/-!
# Stable endomorphisms of arbitrary complex vector spaces

Transparent predicates and statement targets for Renard 2026, Appendix C.II,
Definition and Lemma (i)–(iv), printed pages 276–278 / PDF pages 282–284.
-/

set_option autoImplicit false

namespace Langlands.LinearAlgebra.StableEndomorphism

universe uV uA uB uC

/-- Renard's stability condition, with both kernel and range equalities. -/
def Stable {V : Type uV} [AddCommGroup V] [Module ℂ V] (t : Module.End ℂ V) : Prop :=
  LinearMap.ker t = LinearMap.ker (t ^ 2) ∧
    LinearMap.range t = LinearMap.range (t ^ 2)

/-- A positive power of the actual endomorphism is stable. -/
def EventuallyStable {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (t : Module.End ℂ V) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Stable (t ^ n)

/-- Lemma (i): stability is equivalent to the kernel and range being complementary. -/
def StableIffIsComplStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (t : Module.End ℂ V),
    Stable t ↔ IsCompl (LinearMap.ker t) (LinearMap.range t)

/-- Lemma (ii), for the exact row `A → B → C → 0`. -/
def StableOfRightExactStatement : Prop :=
  ∀ (A : Type uA) (B : Type uB) (C : Type uC)
    [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C]
    (phi : A →ₗ[ℂ] B) (psi : B →ₗ[ℂ] C)
    (fA : Module.End ℂ A) (fB : Module.End ℂ B) (fC : Module.End ℂ C),
    LinearMap.range phi = LinearMap.ker psi →
    Function.Surjective psi →
    fB.comp phi = phi.comp fA →
    fC.comp psi = psi.comp fB →
    Stable fA → Stable fB → Stable fC

/-- Lemma (iii), for the exact row `0 → A → B → C`. -/
def StableOfLeftExactStatement : Prop :=
  ∀ (A : Type uA) (B : Type uB) (C : Type uC)
    [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C]
    (phi : A →ₗ[ℂ] B) (psi : B →ₗ[ℂ] C)
    (fA : Module.End ℂ A) (fB : Module.End ℂ B) (fC : Module.End ℂ C),
    Function.Injective phi →
    LinearMap.range phi = LinearMap.ker psi →
    fB.comp phi = phi.comp fA →
    fC.comp psi = psi.comp fB →
    Stable fB → Stable fC → Stable fA

/-- The kernel chain increases and the range chain decreases, starting at exponent zero. -/
def PowerKernelRangeMonotonicityStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (t : Module.End ℂ V),
    Monotone (fun k : ℕ => LinearMap.ker (t ^ k)) ∧
      Antitone (fun k : ℕ => LinearMap.range (t ^ k))

/-- Lemma (iv): either adjacent equality forces both chains to remain constant. -/
def AdjacentStabilizationStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (t : Module.End ℂ V),
    EventuallyStable t →
    ∀ k : ℕ,
      (LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1)) ↔
        LinearMap.range (t ^ k) = LinearMap.range (t ^ (k + 1))) ∧
      ((LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1)) ∨
          LinearMap.range (t ^ k) = LinearMap.range (t ^ (k + 1))) →
        ∀ m : ℕ, k ≤ m →
          LinearMap.ker (t ^ m) = LinearMap.ker (t ^ k) ∧
            LinearMap.range (t ^ m) = LinearMap.range (t ^ k))

/-- Lemma (iv): the two chains have the same first stabilization index in `ℕ`. -/
def FirstStabilizationIndexStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (t : Module.End ℂ V),
    EventuallyStable t →
    ∃ k₀ : ℕ,
      (∀ m : ℕ, k₀ ≤ m →
        LinearMap.ker (t ^ m) = LinearMap.ker (t ^ k₀) ∧
          LinearMap.range (t ^ m) = LinearMap.range (t ^ k₀)) ∧
      (∀ j : ℕ, j < k₀ →
        LinearMap.ker (t ^ j) ≠ LinearMap.ker (t ^ (j + 1)) ∧
          LinearMap.range (t ^ j) ≠ LinearMap.range (t ^ (j + 1)))

/-- The complete vector-space statement family for Renard's Lemma (i)–(iv). -/
def StableEndomorphismStatement : Prop :=
  StableIffIsComplStatement.{uV} ∧
    StableOfRightExactStatement.{uA, uB, uC} ∧
    StableOfLeftExactStatement.{uA, uB, uC} ∧
    PowerKernelRangeMonotonicityStatement.{uV} ∧
    AdjacentStabilizationStatement.{uV} ∧
    FirstStabilizationIndexStatement.{uV}

end Langlands.LinearAlgebra.StableEndomorphism
