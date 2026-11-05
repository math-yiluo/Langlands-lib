# Finite coordinates for the actual elementary kernel quotient

This internal construction computes the actual kernel-subspace quotient in
finite coordinates. All objects have an arbitrary common universe `u`.

For bases `b` of a `K`-vector space `V` and `c` of `V'`, and a linear map
`φ : V →ₗ[K] V'`, `coefficientMatrix b c φ l j` is the `l`-th coefficient
of `φ (b j)` in `c`. The definition itself needs no finiteness hypothesis.
`coefficientMatrix_apply` assumes a finite source index and proves

`c.repr (φ v) l = ∑ j, b.repr v j * coefficientMatrix b c φ l j`.

The proof expands `v` in `b`, then uses linearity and evaluation of a finite
sum of finitely supported functions. With both index types finite,
`vectorTensorCoordinates_map` proves that applying `ψ ⊗ φ` to a tensor has
`l`-th coordinate `∑ j, coefficientMatrix b c φ l j • ψ (coordinate_b t j)`.
Here `ψ` is an arbitrary linear map between `K`-modules.
`tensorCoordinates_mapCoefficients` proves the corresponding formula for
tensor coordinates over commutative `K`-algebras and an algebra map between
them. Both proofs use tensor induction, the pure-tensor coordinate formula,
and the preceding coefficient identity. Empty finite index types are allowed.

Now let `q : A → B` be an elementary surjection of augmented Artinian tests,
let `W` be a residue-field subspace of its actual kernel, and write `AQ` for
the actual quotient test, `r : AQ → B` for its reduction, and `h : X_AQ → X_A`
for the actual induced scheme morphism. No section of `A → K` is supplied.
`kernelQuotientMatrix q W b c` is the coefficient matrix of the published
actual `kernelLinearMap q W`, for bases of the two actual kernels.

`residueQuotientIso_app` identifies the component of the canonical residue
pushforward isomorphism with `quotientResidueSectionMap`, the actual
restriction between the equal residue inverse-image opens. Its proof unfolds
the canonical pushforward composition and congruence maps.
`residueTensorCoordinates_quotient` specializes the algebra-tensor formula
to that actual restriction and the actual kernel quotient.
`quotientProductMap_coordinates` then proves that, for every open `U`, section
`s` of the source finite product and target index `l`, the `l`-th coordinate
of the actual `quotientProductMap` is

`∑ j, kernelQuotientMatrix q W b c l j • quotientResidueSectionMap f q W U (coordinate_j s)`.

The proof uses the already constructed product-to-tensor equivalences and
their coordinate identities. These section and sheaf calculations require no
flatness, properness or affine-open hypothesis.

The provenance is internal: the results are formal consequences of basis
expansion, tensor induction, the actual residue restriction, and the actual
product-sheaf presentation already implemented in the imported modules.
Cohomology tensor naturality, obstruction naturality and the exact Picard-stack
atlas theorem remain further obligations.
