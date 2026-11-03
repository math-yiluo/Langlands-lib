# Diagonalization of cocharacters of the general linear group

Worker 74. This internal supporting development supplies the rational
diagonalization step in Worker 254's opposite-cell route. It is derived from
the actual split torus, finite free matrix representation, and coefficient
changes in the published Library, together with Mathlib's basis and dimension
results. It makes no claim of being a formalization of a cited source passage.

The main theorem is
`Langlands.GroupScheme.GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter`.
For any field `k : Type u`, any finite coordinate type `n : Type` with decidable
equality, and any actual group-scheme homomorphism
`χ : Gm(Spec k) ⟶ GL_n`, it constructs a point `g` of `GL_n` over `Spec k` and
integers `e : n → ℤ` such that
`χ ≫ (innerIso g).hom = diagonalCocharacter n k e`.
This is equality of actual group-scheme morphisms, so it applies on every test
scheme. There are no perfectness or characteristic hypotheses.

The universal representation matrix is evaluated in the group algebra of the
exponent lattice. Translation by an arbitrary algebra-valued torus point proves
that each coefficient column is an eigenvector after every coefficient extension.
Evaluation at the identity yields the identity matrix. For each coordinate column,
the finite union of its coefficient supports therefore expresses the coordinate
basis vector as a finite sum of coefficient columns; these columns span.

Over a field, Basis.ofSpan selects a basis from those coefficient columns. Equality
of basis cardinalities reindexes it by the original coordinate type. The matrix
whose columns are the selected basis vectors is invertible. Its inverse conjugates
the representation matrix to the diagonal of the corresponding exponent values,
on every commutative test algebra. This is `exists_diagonalizingMatrix` and it
requires no perfectness or characteristic hypothesis.

The interface lemmas identify affine matrices of constant rational points with
coefficient extension of their original matrices, and identify affine matrices
of the published diagonal cocharacter with `diagonalUnits`. The first comparison
uses naturality of the affine point equivalence and the canonical isomorphism
between the identity test scheme and the spectrum of the base algebra. The second
uses the global-section point formula and the canonical global-section/spectrum
isomorphism. The rank-one split-torus comparison is compatible with the published
`gmIso` and sends a multiplicative-group point to its constant one-coordinate
family of units.

For the main theorem, restrict `χ` along the inverse of `gmIso` and apply
`exists_diagonalizingMatrix`. If `B` has the selected weight vectors as columns,
use the actual rational point with matrix `B⁻¹`. Inner conjugation by this point
acts on affine matrices by `M ↦ B⁻¹ M B`, with the same coefficient extensions
on every test algebra. It suffices to compare the two scheme morphisms on the
universal point over `k[T,T⁻¹]`, by the published universal-point extensionality
theorem. The rank-one exponent product is the required integer power, giving the
published diagonal cocharacter. The universal-point factorization then supplies
the asserted equality of scheme morphisms without restricting test schemes to
affine schemes.

This supporting unit does not prove either `GenericCentralizerStatement` or
`StandardParabolicEndpointsStatement`.
