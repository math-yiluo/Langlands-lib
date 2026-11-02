# Finite-unit meromorphic order comparison

The theorem `Langlands.Global.PoleComparison.meromorphicPoleComparison`
proves `MeromorphicPoleComparisonStatement A B` for arbitrary types `A` and
`B` in independent universes. The statement and its hypotheses are unchanged.
The proof uses three auxiliary results in this module.

`omittedProduct_holomorphicUnitAt` shows that the actual finite product
`omittedProduct S f` is analytic and nonzero at `z` whenever every factor
indexed by `S` is. Analyticity comes from Mathlib's
`Finset.analyticAt_fun_prod`. Nonvanishing comes from `Finset.prod_ne_zero_iff`,
because a finite product in `ℂ` is nonzero when each of its factors is. The
empty set is not a special case: its product is the constant function `1`.

`finiteOmittedOrder A` proves the first conjunct (and, with `B`, the second
conjunct). After unfolding `completedProduct` to
`boundary * (omittedProduct S omitted * localFactor)`, Mathlib's
`meromorphicOrderAt_mul_of_ne_zero` is applied twice. The first application
removes the boundary factor, using its own `HolomorphicUnitAt` hypothesis. The
second removes the finite omitted product, using the previous lemma. That
Mathlib identity places no meromorphy hypothesis on the remaining factor. The
equality therefore also holds when the distinguished function is not
meromorphic at `z`. Mathlib's own proof of the identity handles that case.
Multiplication by an analytic function that is nonzero at `z` preserves
meromorphy in both directions (`meromorphicAt_smul_iff_of_ne_zero`). So the
completed product is not meromorphic at `z` either. Mathlib assigns the junk
order `0` to a function that is not meromorphic
(`meromorphicOrderAt_of_not_meromorphicAt`), so both sides equal `0`. The
value `⊤` is different: it is the order of a function that vanishes on a
punctured neighborhood. Hence the first two conjuncts need no meromorphy
premise.

`completedPoleTransfer A B` proves the third conjunct. Applying
`finiteOmittedOrder` on each side rewrites the two distinguished orders as the
orders of the two completed products. Each side uses its own finite set,
omitted family and boundary factor. Mathlib's `meromorphicOrderAt_congr` then
gives equality of those completed orders from their equality on the punctured
neighborhood filter `𝓝[≠] z`. The target's two meromorphy premises stay in the
statement but are not used in this proof, because both Mathlib identities hold
for the totalized order without them. All the unit hypotheses are used: those
on the omitted factors and those on both boundary factors.

The final theorem is the conjunction of these three proofs. The proof supplies
no global functional equation, factor existence or global boundary
nonvanishing. Those remain inputs owned by the statement's consumers.

This is the derived analytic prerequisite motivated by Henniart, *Une preuve
simple des conjectures de Langlands pour GL(n) sur un corps p-adique* (2000),
§§2.5–2.8, printed pp.445–448, as described in the statement's paired
Markdown. The finite-product formulation is internal to the H1 program and is
not a numbered theorem of that article. The proof follows no printed argument.
It directly applies only `Finset.analyticAt_fun_prod`,
`Finset.prod_ne_zero_iff`, `meromorphicOrderAt_mul_of_ne_zero` and
`meromorphicOrderAt_congr`.
