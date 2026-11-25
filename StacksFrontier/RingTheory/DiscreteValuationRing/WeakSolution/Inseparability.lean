module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Weak solutions and solutions after a base change of the fraction field

Let `A → B` be an extension of discrete valuation rings with fraction fields `K → L`. This
file collects three statements about the base-change package of a finite extension `K₁ / K`:
an example showing that inseparability of `K₁ / K` is *necessary* for a weak solution, the
stability of weak unramifiedness under a totally ramified separable base change, and the
Galois action on the rings of the base change.

For a perfect field `k` of positive characteristic `p` and the extension of power-series
rings `k[[x]] → k[[x ^ (1 / p)]]` sending the parameter `x` to the `p`-th power of the new
parameter, every weak solution of the induced extension of Laurent-series fields is
inseparable, and conversely every finite inseparable extension of `k((x))` is a solution.

If `A → B` is weakly unramified and `K₁ / K` is a finite separable extension that is totally
ramified with respect to `A`, then `L ⊗[K] K₁` is a field, the integral closure `A₁` of `A`
in `K₁` and the base change `B₁ = B ⊗[A] A₁` are discrete valuation rings, and `A₁ → B₁` is
again weakly unramified. The canonical image of `B₁` in `L ⊗[K] K₁` is the integral closure
of `B` there, so the same conclusions hold for that literal integral closure.

For a finite normal extension `K₁ / K`, the automorphism group of `K₁ / K` acts on the reduced
base change of `L` and on the integral closures of `A` and of `B`, compatibly with all the
structure maps, and its action on the maximal ideals of the latter integral closure is
transitive.

## Main results

* `IsDiscreteValuationRing.isWeaklyUnramified_iff_ramificationIdx_eq_one`: weak
  unramifiedness of an extension of discrete valuation rings, read as the
  length-theoretic ramification index of the maximal ideal upstairs being one.
* `IsDiscreteValuationRing.weakSolution_isInseparable_and_inseparable_isSolution`: for
  `k[[x]] → k[[x ^ (1 / p)]]` in positive characteristic `p`, every weak solution is
  inseparable, while every finite inseparable extension of `k((x))` is a solution.
* `IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified`:
  stability of weak unramifiedness under a finite separable totally ramified extension.
* `IsDiscreteValuationRing.normal_extension_acts_transitively_on_maximalSpectrum_integralClosure`:
  the compatible actions of `Aut(K₁ / K)` and transitivity on the maximal spectrum.

## Implementation notes

In the example the rings and their fraction fields are allowed to be abstract copies of the
power-series and Laurent-series rings. The algebra equivalences and their compatibility with
the fraction-field embeddings specify the copies canonically, while the equation on the
parameters expresses `k[[x]] → k[[x ^ (1 / p)]]` as the map `x ↦ x ^ p` after renaming the
target parameter. The abstract copies and the finite extension have independent universes; in
the existential base change `L₁` and `B₁` live in the universe of `L ⊗[K] K₁` and `A₁` in that
of `K₁`, and the formal-smoothness test-ring universe `v` is independent of all of these, being
the last universe argument of `IntegralClosureBaseChange.IsSolution`.

For the totally ramified base change, the tensor product is identified with the literal integral
closure through a `B`-algebra equivalence that agrees with the canonical embedding in the field.
Weak unramifiedness is expressed by equality of the extended maximal ideal with the maximal ideal
upstairs; injectivity of both canonical maps is included.

Actions on rings are represented by homomorphisms from the automorphism group to groups of
algebra automorphisms. The induced action on maximal ideals sends an ideal `q` along an
automorphism `g` to the inverse image of `q` under `g⁻¹`.

## References

* [Stacks Project, Tag 09EP](https://stacks.math.columbia.edu/tag/09EP)
* [Stacks Project, Tag 09ER](https://stacks.math.columbia.edu/tag/09ER)
* [Stacks Project, Tag 09EU](https://stacks.math.columbia.edu/tag/09EU)
-/

@[expose] public section

open scoped Pointwise TensorProduct

universe uk uA uB uK uL uK₁ uL₁ uA₁ uB₁ v u

namespace IsDiscreteValuationRing

/-! ### Two readings of the ramification index -/

/-- Weak unramifiedness of an extension of discrete valuation rings, stated with the
length-theoretic ramification index. -/
theorem isWeaklyUnramified_iff_ramificationIdx_eq_one (A B : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    IsWeaklyUnramified A B ↔ (IsLocalRing.maximalIdeal B).ramificationIdx A = 1 := by
  rw [IsWeaklyUnramified, ramificationIndex_eq_ramificationIdx]

/-! ### Inseparability is necessary for a weak solution -/

end IsDiscreteValuationRing
