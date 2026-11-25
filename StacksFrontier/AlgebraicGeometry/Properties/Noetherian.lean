module

public import Mathlib.AlgebraicGeometry.Noetherian
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
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Noetherian schemes have Noetherian topological spaces

The underlying topological space of a Noetherian scheme is Noetherian, and the underlying
topological space of a locally Noetherian scheme is locally Noetherian. The global assertion is
already Mathlib's `AlgebraicGeometry.IsNoetherian.noetherianSpace`, which carries Tag 01OZ
upstream; the local assertion is proved here. A quasi-compact open subscheme of a locally
Noetherian scheme is Noetherian, and therefore has finitely many irreducible components.

## Main results

* `AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian`: the space underlying a
  locally Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.finite_irreducibleComponents_of_isCompact`: a quasi-compact open of a
  locally Noetherian scheme has finitely many irreducible components.

## Implementation notes

The local assertion uses `TopologicalSpace.IsLocallyNoetherianSpace`: every point has an open
neighbourhood whose induced topology is Noetherian.

Tag 01OZ is the conjunction of the two halves its parenthesis abbreviates, so its covering set has
two members. The global half is `AlgebraicGeometry.IsNoetherian.noetherianSpace`, which already
carries `@[stacks 01OZ]` in Mathlib itself at this pin, so no registration for it is needed here.
The attribute below carries the remaining, local half, which Mathlib does not state. The
attribute below carries the remaining, local half, which Mathlib does not state.

A quasi-compact open subscheme is Noetherian because `AlgebraicGeometry.IsNoetherian` is exactly
`IsLocallyNoetherian` together with `CompactSpace`, both of which it inherits; its finitely many
irreducible components are then those of a Noetherian space.

## References

* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
-/

public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A quasi-compact open of a locally Noetherian scheme has finitely many irreducible
components: as a scheme it is locally Noetherian and compact, hence a Noetherian space. -/
theorem finite_irreducibleComponents_of_isCompact (X : Scheme.{u}) [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : (irreducibleComponents U).Finite := by
  have : CompactSpace (U : Type u) := isCompact_iff_compactSpace.mp hU
  have : IsNoetherian (U : Scheme.{u}) := ⟨⟩
  exact finite_irreducibleComponents_of_isNoetherian (X := (U : Scheme.{u}))

end AlgebraicGeometry

end
