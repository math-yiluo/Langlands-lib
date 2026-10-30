# Determinant polynomials on actual local module sections

This internal construction combines the actual section bases and endomorphism
actions of `LocalSectionBasis` with the arbitrary commutative ring determinant
identities of `HodgeDeterminantBaseChange`. It supplies the local polynomial
needed before specializing to Lie modules of abelian schemes.

Fix a scheme `X`, an open `U`, an actual module sheaf `M`, a finite index type `I`,
and a sheaf isomorphism `e` from the free structure-module sheaf on `I` to
`M.over U`. Given a finite family `f` of actual endomorphisms of `M.over U`,
`localSectionDeterminant e f V` is a multivariate polynomial over the actual
structure ring `Γ(X, V.left)` for each smaller open `V` in `Over U`. Its matrix
has entry `(k,l)` equal to the sum over `i` of the constant polynomial with
coefficient the `(k,l)` entry of `f i` acting on sections, multiplied by `X i`.
The definition takes the determinant of this matrix in the constructed section
basis; neither the matrices nor their determinant are supplied as input.

The polynomial agrees with the endomorphism determinant computed in every
finite basis of the same section module. In particular it is independent of the
choice of finite sheaf trivialization on `U`, including its finite index type.
This follows from the published basis independence over arbitrary commutative
rings, rather than detection by polynomial values.

For a morphism `j : V → W` in `Over U`, the structure-sheaf ring map restricts
scalars from `W.left` to `V.left`. Applying its polynomial coefficient map to
the matrix on `W` gives the matrix on `V`: the proof uses the entrywise
endomorphism-matrix restriction theorem, together with preservation of sums,
products, constants and variables by polynomial coefficient mapping. Preservation
of determinants by ring maps then proves the polynomial restriction law.
Taking any monomial coefficient proves the corresponding restriction law for
that coefficient as an actual structure-sheaf section.

Evaluation at any family of scalars on `V.left` is the intrinsic determinant of
the corresponding linear combination of the actual section endomorphisms.
The finite section basis ensures that this is the finite free determinant.
The polynomial has homogeneous support of degree `Fintype.card I`. This
statement allows the zero polynomial and does not assert a nonzero leading
term or an exact total degree.

The scheme, module and basis index live in universe `u`; the finite variable
index may live in an independent universe `v`. There is no affineness,
nonempty-open, nontrivial-ring, reducedness or domain hypothesis. Empty basis
and variable types are allowed. All restriction statements use the same
trivialization and endomorphism family on `U`.

Worker 57 derived this construction from the two imported internal
prerequisites. It proves no comparison with a Hodge polynomial, arithmetic
integrality, PEL representability or existence of a Shimura scheme.
