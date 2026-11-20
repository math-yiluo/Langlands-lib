import Langlands.Representation.FiniteVectors
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Finite orbit spans of Taylor coefficients -/

noncomputable section

namespace Langlands.Global.EisensteinJet

variable {ι R V : Type*} [Monoid R] [AddCommGroup V] [Module ℂ V]

/-- The span of the first `d` coefficients of each of finitely many series. -/
def coefficientSpan (f : ι → ℕ → V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun i : ι × Fin d => f i.1 i.2)

theorem mem_coefficientSpan (f : ι → ℕ → V) (d : ℕ) (i : ι) {n : ℕ} (hn : n < d) :
    f i n ∈ coefficientSpan f d :=
  Submodule.subset_span ⟨(i, ⟨n, hn⟩), rfl⟩

variable [Fintype ι]

/-- If operators act on coefficients by matrix Cauchy products, then the
span of a finite truncation is invariant. -/
def coefficientSubrepresentation (ρ : Representation ℂ R V)
    (f : ι → ℕ → V) (A : R → Matrix ι ι (PowerSeries ℂ))
    (hA : ∀ a j n, ρ a (f j n) =
      ∑ i, ∑ p ∈ Finset.antidiagonal n, PowerSeries.coeff p.1 (A a i j) • f i p.2)
    (d : ℕ) : Subrepresentation ρ where
  toSubmodule := coefficientSpan f d
  apply_mem_toSubmodule a v hv := by
    refine (Submodule.span_le.mpr ?_ :
      coefficientSpan f d ≤ (coefficientSpan f d).comap (ρ a)) hv
    rintro _ ⟨⟨j, n⟩, rfl⟩
    change ρ a (f j n) ∈ coefficientSpan f d
    rw [hA]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun p hp => ?_
    refine Submodule.smul_mem _ _ (mem_coefficientSpan f d i ?_)
    have hle : p.2 ≤ (n : ℕ) :=
      (Nat.le_add_left p.2 p.1).trans_eq (Finset.mem_antidiagonal.mp hp)
    exact hle.trans_lt n.isLt

/-- Every coefficient is finite under the actions preserving the given
finite-dimensional formal family. -/
theorem isFiniteVector_of_coefficient (ρ : Representation ℂ R V)
    (f : ι → ℕ → V) (A : R → Matrix ι ι (PowerSeries ℂ))
    (hA : ∀ a j n, ρ a (f j n) =
      ∑ i, ∑ p ∈ Finset.antidiagonal n, PowerSeries.coeff p.1 (A a i j) • f i p.2)
    (i : ι) (n : ℕ) : FiniteVectors.IsFiniteVector ρ (f i n) := by
  let S := coefficientSubrepresentation ρ f A hA (n + 1)
  let : Module.Finite ℂ S.toSubmodule := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  exact FiniteVectors.isFiniteVector_of_mem ρ S (mem_coefficientSpan f (n + 1) i (Nat.lt_succ_self n))

end Langlands.Global.EisensteinJet
