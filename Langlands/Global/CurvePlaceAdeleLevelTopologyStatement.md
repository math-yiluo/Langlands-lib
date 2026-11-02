# Topology of actual discrete curve-place adelic levels

Author: Worker 208.

`CurvePlaceAdeleLevelTopologyStatement` quantifies arbitrary fields `k` and
`F` with a `k`-algebra structure in a common universe `u`. It concerns the
existing concrete `AlgebraicCurve.Place k F`: nontrivial principal valuation
subrings of `F` containing `k`, with their actual adic completions.

The statement has four conclusions for the actual `CurvePlaceAdeleRing` and
its `curvePlaceAdeleLevel` subrings.

- The canonical `curvePlaceAdeleLevelProductEquiv` is a homeomorphism for the
  level subspace topology and the product of actual completion fields in
  `S` and completed valuation rings outside `S`.
- Each literal transition inclusion for `S ⊆ T` is an open embedding.
- Every element of this restricted product belongs to a finite level.
- A map to any topological space in universe `u` is continuous exactly when
  every restriction to a finite level is continuous.

These are derived restricted-product assertions motivated by Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
printed p.1 and pp.6–8 (Theorem 3.6 and its completed local factors).
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The construction's canonical maps and the Mathlib restricted-product
topology give the objects and topologies; the assertions are meaningful
for these fields without a global-function-field assumption.

The finite set `S` may be empty. Exhaustion here is finite exceptional
support of an element already in the restricted product. It does not
assert finite-pole support for arbitrary elements of `F` or construct a
full-field diagonal. Identification with all conventional global places,
Conrad's nonempty all-place convention, presentation independence,
categorical colimits, nonaffine scheme-point comparisons and the remaining
whole-paper scope are retained as separate obligations.
