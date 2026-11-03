# Real absolute-value places of function fields

This module constructs the equivalence

```text
RealAbsoluteValuePlace F ≃ AlgebraicCurve.Place k F
```

when `k` is a finite field and `F` is a finite extension of the specified
`RatFunc k` algebra, with a compatible `k` algebra. Here the left side is
literally the quotient of all nontrivial real absolute values on `F` by
Mathlib's equivalence relation. There is no discrete, normalized or
nonarchimedean restriction on its representatives. Both fields lie in the same
arbitrary universe. The finite-extension hypothesis is the Mathlib class
`FunctionField k F`; no separability premise is added.

## Provenance and role

This is derived comparison infrastructure for the function-field part of the
adelic construction. It combines the concrete curve-place and valuation-ring
equivalence of `Langlands.Global.FunctionFieldValuationPlaces` with the pinned
Mathlib theory of absolute values, rank-one valuations and normed fields. It
does not claim that Conrad states this implementation-specific equivalence.
Conrad's *Weil and Grothendieck approaches to adelic points* (2011), printed p.1
and pp.6–7, motivates the use of actual global-field places and their completed
local factors. This module supplies the place-index comparison; its completion
and adelic consequences require separate constructions.

The real absolute-value equivalence is the relation

```text
∀ x y : F, a x ≤ a y ↔ b x ≤ b y.
```

Mathlib's `AbsoluteValue.isEquiv_iff_exists_rpow_eq`, in
`Mathlib.Analysis.AbsoluteValue.Equivalence`, proves that for real absolute
values it is exactly equivalence by a positive real power. Thus the quotient
here also agrees with that usual convention.

## Conversion between absolute values and valuations

For any field `F`, `absoluteValueValuation a ha` sends `x` to the nonnegative
real number `a x`, regarded in `ℝ≥0`. Its additional input `ha` is the strong
triangle inequality. The absolute-value zero, one and multiplication laws and
`ha` supply the valuation axioms. `coe_absoluteValueValuation` records that
forgetting the nonnegativity proof recovers `a x` exactly.

If `a` is nontrivial, `absoluteValueValuation_ne_top` proves that its valuation
subring is proper: Mathlib supplies an element with absolute value greater
than one, which cannot belong to the subring.

For a valuation `v` with an actual `v.RankOne` instance,
`rankOneValuationAbsoluteValue v` uses `v.norm`. This is the composition of the
restricted valuation with the strictly increasing rank-one embedding into
`ℝ≥0`, followed by the inclusion into `ℝ`. The ultrametric bound implies the
ordinary triangle inequality by nonnegativity. The remaining absolute-value
axioms follow from multiplication and zero detection for this norm.

`rankOneValuationAbsoluteValue_le_iff` proves that this absolute value induces
exactly the original valuation's comparison preorder. The proof uses strict
monotonicity of `Valuation.RankOne.hom` and `Valuation.restrict_le_iff`.
The following helpers establish the strong triangle inequality,
nontriviality, and equivalence with `v` after conversion back to a valuation.
For nontriviality, the implemented proof takes a nonzero element whose
valuation is not one and uses both comparison directions against `1`.

## Finite constants force the strong triangle inequality

`finiteConstants_absoluteValue_le_one` first proves that an absolute value is
bounded by one on the image of a finite constant field. For a nonzero constant
`x`, finite-field Fermat gives `x ^ (card k - 1) = 1`. Multiplicativity and the
nonnegativity of `a x` imply `a x = 1`; the zero case is separate.
The exponent is positive because a field has more than one element.
`Fintype.ofFinite` is only an internal choice for this proof.

`finiteConstants_absoluteValue_isNonarchimedean` applies that bound to the
images of natural numbers. In the actual normed field `WithAbs a`, all natural
numbers therefore have norm at most one. Mathlib's
`IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one` supplies
the ultrametric instance, and its norm-addition bound is exactly the strong
triangle inequality for `a` on `F`. This argument assumes only finite constants
and a compatible field algebra, without a function-field or rank assumption.
The exported theorem explicitly retains `k` and its finite-field instances.

## Actual places and the quotient

`NontrivialRealAbsoluteValue F` is the subtype of real absolute values
satisfying `IsNontrivial`. `nontrivialRealAbsoluteValueSetoid` is the pullback
of Mathlib's absolute-value setoid along the subtype projection, and
`RealAbsoluteValuePlace F` is its `Quotient`. These definitions themselves
require only a field `F`.

`functionFieldPlaceOfAbsoluteValue k F a` converts an arbitrary representative
to its `ℝ≥0` valuation, using the proved strong triangle inequality. Its
valuation subring is proper by nontriviality. The inverse of
`curvePlaceValuationRingEquiv` then constructs an actual `Place k F`.
The imported comparison proves the principal-ideal property of this subring,
rather than assuming it. `functionFieldPlaceOfAbsoluteValue_mem` states the
literal membership formula `x ∈ O ↔ a x ≤ 1`.
`functionFieldAbsoluteValueValuation_isEquiv_adicValuation` identifies the
resulting place's discrete valuation with the valuation just constructed.

`functionFieldPlaceOfAbsoluteValue_eq_iff` proves that two representatives
give the same place exactly when they are equivalent absolute values.
The forward implication takes equality of the underlying valuation subrings
and invokes `Valuation.isEquiv_iff_valuationSubring`. The reverse implication
uses that same criterion and extensionality of `Place`. The comparison
relations for `ℝ≥0` valuations are definitionally the real comparisons of
the absolute values.

To obtain a representative from a curve place `p`,
`curvePlaceAdicValuationRankOne` realizes its discrete valuation in
nonnegative reals with base two via Mathlib's
`Valuation.IsRankOneDiscrete.rankOne`. This choice supplies a global
rank-one instance for `p.adicValuation`; it is only a normalization choice,
and is not asserted to be the residue-cardinality normalization.
`curvePlaceRealAbsoluteValue k F p` is the resulting nontrivial absolute
value. Converting it back gives `p`, since its valuation has the same
comparison preorder and the published
`Place.adicValuation_valuationSubring` identifies its valuation ring.

Finally, `realAbsoluteValuePlaceCurvePlaceEquiv` descends the forward
construction by `Quotient.lift`. Its inverse takes the class of the chosen
representative of `p`. The right inverse is the preceding place identity.
The left inverse follows by quotient induction and
`functionFieldPlaceOfAbsoluteValue_eq_iff`. The final two simp lemmas expose
the forward map on any representative and the inverse on every curve place.

## Scope

The module proves the actual place-index equivalence and the valuation
comparison on the original field. It constructs no map between completed
fields, restricted products, their topologies or scheme-valued points.
Local compactness, a diagonal-discreteness theorem, the comparison of full
adelic rings, and Conrad's nonaffine and algebraic-space assertions remain
separate obligations of the encompassing program.
