# Hermitian weights from a normal cocharacter value

This internal construction by Worker 1655 proves that a cocharacter of the
actual general linear group scheme over an arbitrary-universe `RCLike` field
has Hermitian Laurent weight projectors whenever its matrix value at the
positive scalar two is normal. It uses the Laurent projectors of
`GeneralLinearCocharacterWeights` and the Hermitian predicate of
`UnitaryCocharacterDiagonal`. It does not assert the existence of a
star-stable realization for an arbitrary reductive group and specified Levi.

## Normal operators and projectors

`adjoint_apply_eq_conj_smul_of_normal` starts with a bounded normal operator
on a complete real or complex inner product space. If `T x = c • x`, the
operator `T - c • 1` is normal: its two summands are normal, and `T`
commutes with the adjoint of the scalar operator. Equality of the kernels
of a normal operator and its adjoint gives
`T.adjoint x = star c • x`.

`inner_eq_zero_of_normal_eigenvectors` applies the defining adjoint inner
product identity to eigenvectors for two distinct eigenvalues. The resulting
scalar equality forces their inner product to vanish.

`hermitian_projectors_of_normal_separating_action` concerns a possibly
infinite family of matrices `F a`. The hypotheses say
`F a * F b = if a = b then F a else 0`, that a finite subfamily sums to
the identity, and that a normal matrix `A` satisfies
`A * F a = c a • F a` for an injective scalar function `c`. No projector
is required to be nonzero.

The proof transports `A` to its continuous operator on Euclidean space
using `Matrix.toEuclideanCLM`. Its star algebra structure preserves normality.
The range of each `F a` consists of eigenvectors of this operator. Distinct
projector ranges are therefore orthogonal. For a vector in the kernel of
`F a`, the finite sum decomposition into projector images has zero `a`
component and is orthogonal to the range of `F a`. The characterization
of symmetric idempotents by orthogonality of range and kernel proves
symmetry, and the Euclidean matrix comparison gives Hermitianity.

## Evaluation of the actual cocharacter

`positiveTwoUnit` is the scalar `2` bundled as a unit.
`cocharacterEvalUnit` is Laurent evaluation at any scalar unit, bundled as
an algebra homomorphism. Its monomial formula sends a Laurent monomial
with coefficient `r` and exponent `a` to `r * t^a`.

`cocharacterUnitsHom_eq_sum_weightProjector` applies the published
naturality of the actual cocharacter point map to this evaluation homomorphism
and to the universal Laurent unit. Entrywise evaluation of the finite Laurent
expansion gives the literal matrix identity
`χ(t) = ∑ a ∈ support, t^a • E_a`.
`cocharacterUnitsHom_mul_weightProjector` multiplies this identity by `E_a`.
The published projector multiplication identities eliminate every other
summand. For an exponent outside the support, its projector is zero.

The proposition `HasNormalPositivePoint χ` means exactly that the matrix
`cocharacterUnitsHom χ 𝕜 (positiveTwoUnit 𝕜)` is normal for conjugate
transpose. Its theorem `hasHermitianWeightProjectors` applies the preceding
projector result to this matrix and the eigenvalues `2^a`. These eigenvalues
are distinct: integral powers of the positive real number two are injective,
and the canonical embedding of the reals in an `RCLike` field preserves
integer powers and is injective.

This unit establishes a sufficient condition for the existing Hermitian-weight
predicate. It neither assumes nor constructs a compact subgroup or an Iwasawa
decomposition. Its provenance is the implemented linear-algebra argument
above and the imported, actual scheme-point Laurent construction.
