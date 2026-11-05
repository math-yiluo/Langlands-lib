# Polynomial pullback along rectangular intertwiners

This internal construction supplies polynomial substitution for a linear map
between different finite coordinate spaces. Its base ring has arbitrary
universe `u`; the finite coordinate types are small, as in the existing
geometric-reductivity target.

`rectangularPullback C F` substitutes the row linear forms of a matrix
`C : Matrix m n k` into a polynomial with variables indexed by `m`, producing
a polynomial with variables indexed by `n`. The evaluation lemma holds after
every homomorphism from the commutative base ring into any commutative ring.
The homogeneous-degree lemma follows from substitution by degree-one forms.
As in Mathlib's predicate, the zero polynomial may have any specified degree.
The base-ring evaluation formula identifies the value at `v` with the value of
`F` at `C *ᵥ v`.

For a field and an affine acting group, an existing affine-test intertwiner
between two actual matrix representations gives the intertwining equation
on every relative test scheme, by `Intertwines.points`. That equation proves
that rectangular pullback preserves the unchanged all-test
`IsInvariantPolynomial` predicate. No affineness or reducedness restriction is
placed on the test scheme. The separator lemma combines this invariance with
homogeneity and the value formula: a supplied degree-`d` invariant nonzero at
`C *ᵥ v` gives a degree-`d` invariant nonzero at `v`. A supplied positive degree
therefore remains positive.

`Intertwines.isFixedVector` sends a supplied fixed vector to a fixed vector.
It uses the scalar-extended matrix identity and compatibility of matrix-vector
multiplication with a ring homomorphism. The fixedness hypotheses and conclusion
both use all relative scheme tests.

The provenance is internal: the construction uses polynomial substitution,
matrix associativity and the published affine-to-all-test intertwiner bridge.
It requires neither injectivity nor surjectivity of `C`. It supplies no initial
separating invariant, Steinberg module or reductive structural cover, and does
not prove Haboush's theorem.
