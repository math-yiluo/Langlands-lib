# Uniqueness of supplied full fppf quotients

For any group scheme `G` over a scheme `S` in universe `u`, two supplied
quotients `q : G → Q` and `r : G → R` satisfying
`RelativeRoot.IsFppfQuotient F` for the same subgroup functor `F` have a
canonical actual group-scheme isomorphism
`FppfQuotientComparison.fppfIso hq hr : Q ≅ R`. Its composite with `q` is
`r`, and that equation characterizes the isomorphism uniquely.

Here the full quotient predicate consists of flatness, surjectivity,
local finite presentation, and equality of the all-test range of the
actual kernel with `F`. The construction uses exactly those hypotheses.

The published `FppfQuotientComparison.kernel_comp` says that `r` kills the
kernel of `q`. `FppfHomDescent.hom` therefore constructs `fppfHom`, with its
factorization equation `fppfHom_fac`. Applying this construction in both
directions gives the two inverse maps. The published `hom_ext` proves the
inverse laws and uniqueness by cancellation with the flat surjective
quotient maps.

This is an internal derived extension of the published comparison
construction using fppf homomorphism descent. It constructs no quotient
and imposes no hypothesis of quasi-compactness on either supplied quotient
map.
