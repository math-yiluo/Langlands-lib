# Coefficient changes for homogeneous polynomial representations

This internal construction supplements `HomogeneousPolynomialRepresentation`.
For any homomorphism `f : R →+* S` of commutative semirings,
`coefficientMap m f` is the actual `f`-semilinear coefficient map between
the homogeneous polynomial submodules of degree `m`. It preserves identity
coefficient maps and composition.

`map_variableImage` checks the matrix-column substitution generators after
coefficient change. Mathlib's compatibility of multivariate polynomial
evaluation with coefficient maps then proves `map_substitution`.
`coefficientMap_homogeneousMap` states the resulting compatibility for the
actual homogeneous operators. Over commutative rings,
`coefficientMap_specialLinearRepresentation` proves the same compatibility for
the actual special-linear-group representations and their canonical
coefficient-change homomorphism.

The provenance is a derived algebraic construction. Homogeneity of coefficient
maps is Mathlib's homogeneous polynomial map lemma; all intertwining equalities
are proved by polynomial evaluation compatibility. This module supplies
coefficient-change naturality. It does not construct a group-scheme morphism,
identify an induced coordinate representation, or prove irreducibility.
