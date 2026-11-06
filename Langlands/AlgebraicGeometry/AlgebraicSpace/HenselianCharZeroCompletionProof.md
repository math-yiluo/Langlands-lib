# Henselian valued fields of characteristic zero are algebraically closed in their completion

Worker 105 authored the shared proof draft. Worker 1607 checked the proof against
the published target and prepared it for independent review.

`henselianCharZeroAlgebraicallyClosedInCompletion` proves
`HenselianCharZeroAlgebraicallyClosedInCompletionStatement` (from
`Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianFinitePointProperStatement.lean`).
Let `K` be a nontrivially normed field that is henselian in Conrad's sense
(`IsHenselianValuedField K`) and has characteristic zero. Then the algebraic closure of
`K` in its completion `UniformSpace.Completion K` is `⊥`: every element of the
completion that is algebraic over `K` lies in `K`.

This is the characteristic-zero case of the remark after Corollary 5.12 in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.20. The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

## Proof

The published theorem `henselianSeparablyClosedInCompletion` (from
`Langlands/AlgebraicGeometry/PointTopology/HenselianEtalePointProof.lean`) says that the
separable closure of a henselian valued field `K` in its completion is `⊥`. So it is
enough to show that the algebraic closure of `K` in the completion is contained in the
separable closure.

Let `x` be an element of the completion that is algebraic over `K`
(`mem_algebraicClosure_iff`). Then `x` is integral over `K`, so its minimal polynomial is
irreducible (`minpoly.irreducible`). A field of characteristic zero is perfect (Mathlib's
instance `PerfectField.ofCharZero`), and over a perfect field every irreducible
polynomial is separable (`Irreducible.separable`). Hence `x` is separable over `K` and
lies in the separable closure (`mem_separableClosure_iff`). Combined with the published
theorem, this gives `algebraicClosure K (UniformSpace.Completion K) = ⊥`
(`eq_bot_iff`).

Conrad gives no argument for the remark; this is the standard one. The excellent
valuation-ring case of the remark is not stated in the Library and is not proved here.
