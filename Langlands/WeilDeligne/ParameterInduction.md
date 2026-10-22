# Induction of open-inertia Weil–Deligne parameters

Worker 17 authored this construction. `parameterInduce` constructs the actual
induced pair and proves its open-inertia certificate using the underlying
finite representation's induction theorem. The ambient inertia subgroup and
finite-index inducing subgroup are explicitly open, and the source inertia is
their intersection as a subgroup of the inducing group.

`parameterInduceClass` uses the proved induction of pair equivalences to descend
to genuine parameter classes. `parameterInduceClassOfRank` supplies the rank
indexed operation from rank `n` to rank `S.index * n`, using the actual dimension
formula. Rank zero is permitted. Monodromy is the weighted operator
`N_ind(f)(g) = nu(g) N(f(g))`, including nonzero monodromy.

This is the assembly of the two paired induction modules into Tate's algebraic
parameter convention: *Number theoretic background*, Corvallis Part II,
printed pages 9–10, §2.1, and printed page 20, §4.1.2. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
No additional equivalence theorem is placed in a structure field.
The actual local Weil subgroup and its norm and inertia compatibility must be
provided by the separately tracked local specialization. Preservation of
Frobenius semisimplicity, comparison with usual-topology continuity, and
induction identities beyond the intrinsic functor laws are not asserted here.

## Included algebraic induction module

`Langlands.WeilDeligne.Induction` is included in this contribution. It
imports `Langlands.Weil.Representation.Induction` and constructs the
weighted pair with all nilpotence, covariance, map, functor, equivalence
and quotient obligations proved. This parameter module imports that
construction, `Langlands.WeilDeligne.Parameters`, and
`Langlands.Weil.Representation.InductionTopology` to supply the explicit
open-inertia and rank-indexed wrappers.
