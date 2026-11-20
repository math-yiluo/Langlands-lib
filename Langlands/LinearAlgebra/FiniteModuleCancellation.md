# Cancellation of finite-dimensional modules

`Langlands.FiniteModuleCancellation.nonempty_linearEquiv_of_copies` shows that if
`d` copies of an `R`-module `M` are isomorphic to `d` copies of `N`, where `d > 0`,
then `M` and `N` are isomorphic. Here `R` is an algebra over a field `K`, and the
modules have finite dimension over `K`. This is an internal application of the
Krull–Schmidt argument. The module also gives the form for families of linear
operators used in `Langlands.BaseChange.CyclicNormFieldConjugacy`.

The finite dimension over `K` implies that each module is Noetherian and Artinian
over `R`. For a nonzero indecomposable module `A`, the Fitting decomposition
splits the kernel and image of a sufficiently high positive iterate of an
endomorphism. Since one summand is zero, the endomorphism is invertible or
nilpotent. Thus either it or its difference from `1` is a unit, which makes the
endomorphism ring local.

An isomorphism `A × M ≃ A × N` can cancel such an `A`. Compose the first column
of the isomorphism with the first row of its inverse. The two resulting
endomorphisms of `A` sum to `1`, so at least one is invertible. If the first one
is invertible, the upper left entry of the isomorphism is bijective, using
finite dimension. If the second one is invertible, adding a suitable map
from the second component of the target to the first makes the upper left
entry the identity. A second elementary transformation eliminates the lower
left entry. The map on the second components is then bijective. Reindexing
products iterates this cancellation on any number of copies of `A`.

The proof of the copies theorem inducts on `dim_K M`. A nonzero `M` has an
indecomposable direct summand `A` by choosing a nonzero direct summand of least
positive dimension. The given isomorphism exhibits `A` as a retract of the
product of the copies of `N`. The section and retraction produce a finite sum of
endomorphisms of `A` equal to `1`. Some summand is invertible by locality, so
`A` splits off one copy of `N`. Cancel all copies of `A` and apply the induction
hypothesis to the two complements. When `M` is zero, the positive number of
copies implies that `N` is zero as well.

For `exists_intertwiningEquiv_of_copies`, the operators give module actions of
the free `K`-algebra on their indexing type. An intertwiner of the operators
intertwines the free-algebra actions by induction on algebra expressions. After
cancelling copies, restricting scalars gives a `K`-linear isomorphism that
intertwines every original operator.
