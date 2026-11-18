import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Separation of bounded algebra characters in absolutely convergent sums

For each place `x`, the values `χ i x h` at a fixed algebra element `h` are uniformly
bounded in `i`, and a single element `h'` realizes their complex conjugates for every
`i`. If all finite-place products of character values have weighted sum zero against
the summable coefficients `c`, the coefficients have sum zero on each fibre of the
character family.

The paired Markdown explains the separation of Hecke eigenvalues in the trace
formula comparison and gives a proof sketch for this derived statement.
-/

universe u v w

namespace Langlands.TraceFormula

/-- For a summable complex family `c` and algebra characters `χ` that satisfy the
uniform bound and simultaneous conjugation conditions at each place, vanishing of
all finite-place product tests implies `HasSum` with value zero on every fibre
`{i : ι // ∀ x, χ i x = χ i₀ x}`. -/
def BoundedCharacterSeparationStatement : Prop :=
  ∀ (ι : Type u) (W : Type v) (H : W → Type w) [∀ x, Semiring (H x)] [∀ x, Algebra ℂ (H x)]
    (χ : ι → (x : W) → (H x →ₐ[ℂ] ℂ)) (c : ι → ℂ),
    Summable c →
    (∀ (x : W) (h : H x), ∃ C : ℝ, ∀ i, ‖χ i x h‖ ≤ C) →
    (∀ (x : W) (h : H x), ∃ h' : H x, ∀ i, χ i x h' = starRingEnd ℂ (χ i x h)) →
    (∀ (T : Finset W) (h : (x : W) → H x),
      HasSum (fun i => c i * ∏ x ∈ T, χ i x (h x)) 0) →
    ∀ i₀ : ι, HasSum (fun i : {i : ι // ∀ x, χ i x = χ i₀ x} => c i) 0

end Langlands.TraceFormula
