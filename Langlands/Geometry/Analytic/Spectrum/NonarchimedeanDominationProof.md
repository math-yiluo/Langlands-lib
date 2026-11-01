# Multiplicative domination by minimal ultrametric seminorms

`Langlands.Analytic.BanachSpectrum.nonarchimedeanDomination` proves
`NonarchimedeanDominationStatement` at every universe `u`: a normalized
nonarchimedean ring seminorm `p` on a commutative ring dominates a
nonarchimedean multiplicative ring seminorm.

The proof works with real-valued functions on the underlying ring. The
private predicate `dominationConditions` records vanishing at zero,
normalization at one, the strong triangle inequality, invariance under
negation, submultiplicativity, nonnegativity and pointwise domination by
`p`. These conditions define a closed set in the product topology: each
equation or weak inequality is closed because evaluation, addition,
multiplication and maximum are continuous. The set lies in the product
of the compact intervals `[0, p a]`, so it is compact. It is nonempty
because `p` itself satisfies the conditions.

The private lemma `exists_minimal_of_compact_functions` applies Zorn's
lemma to this pointwise order, with its direction reversed. For a
nonempty chain, the sets consisting of elements of the compact set
lying below a chain element are nonempty compact closed sets, directed
by reverse inclusion. Their intersection is nonempty and supplies a
lower bound in the same set. The empty chain has a lower bound by the
original nonemptiness. Zorn therefore supplies a pointwise minimal
function satisfying `dominationConditions`. The strong triangle
inequality and nonnegativity imply the ordinary triangle inequality,
so the function defines a `RingSeminorm q`. Any other normalized
nonarchimedean ring seminorm below `q` equals `q` by minimality.

Mathlib's `smoothingSeminorm q` is normalized, nonarchimedean and
pointwise bounded by `q`. Normalization follows directly from its
defining infimum at one. Minimality identifies it with `q`, and
`isPowMul_smoothingFun` consequently makes `q` power multiplicative.
For an element `a` with `q a ≠ 0`, Mathlib's
`seminormFromConst` construction is again normalized, nonarchimedean
and bounded by `q`, and is multiplicative with respect to multiplication
by `a`. Minimality identifies this seminorm with `q`, giving
`q (a * b) = q a * q b` for all `b`. If `q a = 0`, the same equality
follows from submultiplicativity and nonnegativity.

The resulting multiplicative seminorm retains the strong triangle
inequality and the original bound by `p`. The proof imposes no
topology, completeness or domain hypothesis on the ring and no
nontrivial valuation assumption. It uses the standard Lean axioms
`propext`, `Classical.choice` and `Quot.sound`.

This is an internal auxiliary proof using Mathlib's seminorm and
compactness APIs. It does not claim to transcribe a literature proof,
construct a tensor seminorm or prove the host point-amalgamation
statement.
