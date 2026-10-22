# Ordinary-to-Tate comparison on cocycles and connecting maps

Proof author: Worker 45. Proof audit and documentation preparation: Worker 54.

The theorem `Langlands.Tate.ordinaryTateBoundaryLaws` proves the published
proposition `Langlands.Tate.OrdinaryTateBoundaryLaws` exactly. This is an internal
compatibility proof for the published ordinary-to-Tate comparison.

The cycle comparison retains an ordinary cocycle as the identical cochain in
Mathlib's norm-spliced Tate complex. Its positive-degree homology formula unfolds
Mathlib's restriction comparison and uses naturality of the homology projection.
At degree zero the proof composes the ordinary projection with `H0Iso`, cancels
the cocycle-to-invariants isomorphism, and applies the published
`zeroClass_eq_cycleClass`. Injectivity of cycle inclusion identifies the same
cochain on both sides. The cases give `ordinaryToTate_π` in every natural degree.

`ordinaryToTate_cyclesMk` expresses this result for a cochain with zero
differential, using injectivity of cycle inclusion to identify its constructed
cycles. `ordinaryToTate_delta` then compares actual connecting maps for every
short exact sequence and every nonnegative degree. Choose a cocycle representative
and lift its cochain through the degreewise surjective last map. Exactness lifts
the differential through the first map. The ordinary and Tate complexes have
identical cochains, maps and differentials in these degrees. Thus their actual
connecting-map representative formulas use precisely the same lifts. Applying
the cocycle formula proves the commuting square, including degree zero.
No scalar splitting or tensor exactness hypothesis is used.

The Lean statements use arbitrary common universe `u`. Their mathematical
normalization is the published `ordinaryToTate` construction. The final theorem
collects the cocycle representative identity and the connecting-map identity into
the exact proposition from `OrdinaryTateBoundaryStatement`, without adding any
hypotheses.

The proof imports the published target and its dependencies unchanged. The
helper `ordinaryTateCycles` is an actual morphism to the cycles of the Tate
complex, defined by lifting the ordinary cocycle inclusion. The lifts used for
connecting maps follow from degreewise short exactness; they are chosen for
each representative and do not constitute a splitting of representations.
Both boundary calculations use Mathlib's short-exact-complex `δ_apply`
formula, directly for ordinary cohomology and through `delta_cycleClass` for
Tate cohomology, so their signs agree without an additional convention.

The provenance is the published `OrdinaryTateComparison` construction and
`OrdinaryTateBoundaryStatement` specification; this module supplies an internal
proof of those compatibility laws. The original mathematical normalization
and its source locations are documented in those imported modules. No cup
product compatibility is asserted here.
