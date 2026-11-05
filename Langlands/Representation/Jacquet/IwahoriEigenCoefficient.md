# Exact eigen-coefficients from supplied Iwahori contraction data

Author: Worker 1680.

This internal supporting unit derives ordinary Jacquet eigenvector lifts and
exact smooth matrix coefficients from the published compact compression and
Iwahori contraction APIs. It is an abstract-group version of the algebraic
lift and averaging steps used in the published
`ProductLeviNecessityEigen.lean`; it does not use its block-matrix geometry.
No existence of Iwahori contractions, reductive structural theorem, analytic
integrability implication or full Casselman criterion is asserted.

`iwahoriStableImageJacquetEquiv` is the actual linear map
`stableImageJacquetMap` equipped with the inverse guaranteed by
`stableImageJacquetMap_bijective_of_iwahoriContraction`. Its domain is the
intersection of the ranges of all powers of the compact compressed action.
Its codomain is the submodule of ordinary, unnormalized coinvariants fixed by
the Levi intersection of the specified compact open subgroup. The source
fixed-vector space is assumed finite dimensional. Its displayed application
law identifies the map with the actual coinvariant projection.

`exists_compressedAction_eigenvector_of_jacquet_eigenvector` lifts a supplied
nonzero Jacquet eigenvector through this equivalence. The lift is nonzero
because its coinvariant image is the given nonzero vector. Compression
preserves its own stable image. The published quotient compatibility makes
the images of the compressed lift and its scalar multiple equal.
Injectivity on the stable image proves the required compression eigenvector
equation. The lift projects to the original vector, not merely to an
unspecified eigenvector.

`exists_eigen_coefficient_of_compressedAction_eigenvector` works for any
compact open subgroup and element for which compression respects powers.
An algebraic functional nonzero at the supplied vector exists by separation
by the full algebraic dual. Composing it with the normalized compact average
produces a functional invariant under the compact open subgroup; averaging
fixes the supplied vector, so the functional remains nonzero there.
Its invariance under the open subgroup implies smoothness for the
contragredient action. Induction on powers of the compression and the
assumed power law then give the exact coefficient formula
`ℓ(ρ(g^n)x) = λ^n ℓ(x)` for every natural number `n`.

`exists_eigen_coefficient_of_jacquet_eigenvector` combines the two steps,
using the published Iwahori contraction power law. The resulting vector is
fixed by the specified compact open subgroup and still projects to the
original Jacquet vector. The smooth functional is invariant under the same
subgroup and does not vanish on that vector.

The ambient group and representation carrier have independent universes.
The ambient group is a topological group, the representation is smooth over
the complex numbers, the open subgroup is compact, and the stated
factorization, contraction and normalizer hypotheses are supplied.
No global Jacquet admissibility or generalized weight decomposition is used.
