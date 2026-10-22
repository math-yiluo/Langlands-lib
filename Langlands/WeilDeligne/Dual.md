# Negative-transpose duality of Weil–Deligne pairs

Worker 17 authored this construction. `dual A` has the actual full
dual vector space, the inverse-element dual action, and monodromy
`-A.monodromy.dualMap`, which is the negative transpose.

The nilpotence certificate proves by induction that transpose commutes
with powers of a single endomorphism, transfers a nilpotence exponent
from `N`, and uses preservation of nilpotence under negation. The
covariance certificate evaluates a functional at a vector and applies
the original equation `r(g) N r(g⁻¹) = nu(g) N`. The norm character
remains `nu`. No characteristic-zero hypothesis is needed for these
algebraic certificates.

`dualMap` uses the published dual intertwiner and checks the reversed
monodromy square by evaluation. `dualFunctor` proves the opposite-category
identity and composition laws. `dualEquiv` reverses a genuine pair
equivalence; its inverse supplies the quotient compatibility for
`dualClass`. Carrier universes are independent and zero rank is allowed.

The negative sign is fixed by the invariant evaluation pairing:
`(-transpose N)(ell)(v) + ell(N(v)) = 0`. Thus this is the dual
infinitesimal action on the additive part of the Weil–Deligne group,
not a separately chosen monodromy endomorphism. Tate, *Number theoretic
background*, Corvallis Part II, printed page 20, §§4.1.1–4.1.2, identifies
the group-scheme action as `exp(aN) r(w)`. Dualizing the additive action
gives this sign. The sign formula and constructor certificates here are
direct algebraic derivations, not a quotation of an unproved comparison.
Literature ID `tate-1979-number-theoretic-background`, PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

This module imports `Langlands.WeilDeligne.Basic` and
`Langlands.Weil.Representation.Dual`. The latter imports the unchanged
Worker 0 module `Langlands.Representation.Dual.Definitions` and records
the full algebraic-dual convention from Casselman. No
smooth-contragredient theorem, topology comparison, semisimplification
existence, or parameter-preservation result is assumed.
