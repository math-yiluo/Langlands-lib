module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Reducedness ascends along a flat ring map with reduced fibres

If `φ : R → S` is a flat map of Noetherian rings, `R` is reduced and every fibre ring
`κ(𝔭) ⊗_R S` is reduced, then `S` is reduced.

## Main results

* `Stacks.Flatness.ReducedFibreAscent.isReduced_left_of_tensor`: for `A` flat over `R` and
  `R → T` injective, if `A ⊗[R] T` is reduced then `A` is reduced.
* `Stacks.Flatness.ReducedFibreAscent.isReduced_of_flat_of_forall_isReduced_fiber`: a flat
  `R`-algebra whose fibre rings at a finite family of primes of `R` with zero intersection are
  reduced is reduced.
* `isReduced_of_flat_of_isReduced_fiber`: a flat ring map of Noetherian rings with reduced source
  and reduced fibre rings has reduced target.

## References

* [StacksProject 0C21](https://stacks.math.columbia.edu/tag/0C21)

## Tags

reduced ring, flat ring map, fibre ring, ascent, minimal prime, Noetherian ring
-/

@[expose] public section

universe u v w

@[expose] public section

namespace Stacks.Flatness.ReducedFibreAscent

open scoped TensorProduct

/-- In a reduced commutative ring, an element lying in every minimal prime is zero. -/
public theorem eq_zero_of_forall_mem_minimalPrimes {R : Type*} [CommRing R] [IsReduced R] {r : R}
    (hr : ∀ q ∈ minimalPrimes R, r ∈ q) : r = 0 := by
  have hmem : r ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.2 hr
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes from rfl, Ideal.sInf_minimalPrimes,
    Ideal.radical_bot_of_isReduced] at hmem
  simpa using hmem

end Stacks.Flatness.ReducedFibreAscent

end

@[expose] public section

end
