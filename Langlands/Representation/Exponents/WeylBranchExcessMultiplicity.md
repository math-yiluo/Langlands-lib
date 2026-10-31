# Strict multiplicity excess lies in another graded piece

Module `Langlands.Representation.Exponents.WeylBranchExcessMultiplicity`.

This module provides the multiplicity bookkeeping step of the branch selection
in Silberger 1978, Lemma 5.6. Suppose the ambient Jacquet module has a finite
filtration whose distinguished (coarse) graded piece is the inner Jacquet
module, and suppose an irreducible representation occurs more often in the
ambient module than in the inner one. Then it must occur in a different
graded piece. All multiplicities are actual Jordan–Hölder multiplicities
`HasJordanHolderMultiplicity A τ m`: `A` has an actual composition series in
which exactly `m` factors are equivalent to `τ`. They are not Hom dimensions
or label counts. The conclusion uses the published predicate
`Langlands.WeylBranchPieces.IsSubquotient A X` from
`Langlands.Representation.Exponents.WeylBranchPiecesStatement`: `X` is an
actual quotient of an actual subrepresentation of `A`.

All representations are complex representations of an arbitrary group `G`.
The carriers of the filtered representation, of `τ`, and of the comparison
representation `X` lie in independent universes. No statement in this module
assumes that `τ`, the graded pieces, or `X` are irreducible, and no
finite-length hypothesis is placed on the graded pieces. Finite length of the
pieces follows from the ambient composition series.

## Declarations

- `isSubquotient_gradedRepresentation s j`: the `j`th graded quotient of an
  actual object filtration `s : ObjectRepFiltration A n` is an actual
  subquotient of `A`. This is the published
  `isSubquotient_graded` at the single object of the constant functor.

- `isSubquotient_of_factorMultiplicity_pos s h`: if a filtration `s` of `A`
  has at least one graded quotient equivalent to `τ`
  (`0 < s.factorMultiplicity τ`), then `τ` is an actual subquotient of `A`.
  Positivity of the `Nat.card` gives an index `j` and an equivalence from the
  `j`th graded quotient to `τ`. The previous lemma and
  `IsSubquotient.of_equiv_right` then finish.

- `exists_ne_isSubquotient_gradedRepresentation_of_lt hM s j₀ φ h₀ hlt`: let
  `HasJordanHolderMultiplicity A τ M`, let `s` be an actual finite filtration of
  `A` (repeated steps and zero graded pieces are allowed), and let `φ` be an
  equivalence from the `j₀`th graded quotient to a representation `X` with
  `HasJordanHolderMultiplicity X τ m₀` and `m₀ < M`. Then some index `j ≠ j₀`
  has `τ` as an actual subquotient of its graded quotient.

- `objectFiltration s Y`: the objectwise filtration of `F.obj Y` given by a
  natural filtration `s : RepFunctorFiltration F n` at an object `Y`, built
  with `ObjectRepFiltration.ofSubrepresentations` from the subspaces
  `(s.step k).obj Y`. Its graded quotients are definitionally the graded
  functors of `s` evaluated at `Y`.

- `IsGluedFrom.exists_ne_isSubquotient_piece_of_lt h Y hM i₀ h₀ hlt`: the
  same statement for the published unordered gluing relation
  `IsGluedFrom F pieces`. If `τ` has multiplicity `M` in `F.obj Y` and the
  piece `i₀` has multiplicity `m₀ < M` at `Y`, then `τ` is an actual
  subquotient of `(pieces i).obj Y` for some `i ≠ i₀`.

## Reused excess proofs

The two excess declarations are argument-order wrappers around
`exists_isSubquotient_graded_of_multiplicity_excess` and
`IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess` from
[Actual subquotients selected by multiplicity excess](WeylBranchMultiplicityExtraction.md).
Their hypotheses, independent carrier universes and conclusions are unchanged.

The existing graded proof uses `jordanHolderFiltrationDecomposition` to obtain
finite composition series for the grades and counts summing to the ambient
multiplicity. Transport and uniqueness identify the distinguished count with
`m₀`. If every other count were zero, the sum would be `m₀`, contradicting
`m₀ < M`. A positive other count supplies an actual subquotient of that grade.
The existing glued proof evaluates the natural filtration at `Y`, applies this
argument at the inverse image of `i₀` under its indexing permutation, and
transports the resulting subquotient to the corresponding named piece.

The more general positive-factor-count lemma and the named `objectFiltration`
construction remain in this module.

## Provenance

This is internal algebraic infrastructure and makes no new claim about the
literature. It is the elementary counting step behind Silberger's selection of
the responsible Weyl piece in Lemma 5.6 (Silberger 1978, printed p. 101): when
the ambient multiplicity strictly exceeds the multiplicity of the
distinguished piece, the excess lies in another piece. Additivity, uniqueness
and transport of the multiplicities are the published Library results named
above.
