# Extremal coordinates from a supplied highest-weight representation

This internal derived construction by Worker 1369 converts a supplied actual
highest-weight representation at integral rho into the representation data used
by `IsRootDatumOf.canonicalRhoBigCellGeometricData`. It proves no representation
existence theorem and does not prove `SteinbergBigCellStatement`.

Fix a field `k`, an affine group scheme `G` over `Spec k`, a supplied
`SplitPinning p`, a finite root index, and `hspan : p.rootDatum.corootSpan ℤ = ⊤`.
Write `r = IntegralWeylVector.rho p.rootDatum p.base hspan` and
`nu = p.rootDatum.Polarization r`. No algebraic closedness or characteristic
assumption is required for this conditional construction.

The primary definition `SplitPinning.negativeRhoExtremalRepresentationData`
starts with `rho : MatrixRepresentation G n` and `p.IsHighestWeight rho r`,
where `n` is any finite small type with decidable equality. It produces an actual
record `SplitPinning.NegativeRhoExtremalRepresentationData p hspan n`. Its
fields are an actual matrix representation `sigma` on the same index type,
integer exponents `e`, and an index `a`, with proofs of precisely:

- The composite of the actual cocharacter `nu`, the original torus inclusion,
  and `sigma` is `GeneralLinear.diagonalCocharacter n k e` as a group-scheme
  morphism.
- `e a < e c` for every `c ≠ a`.
- On every relative test scheme `V` and every torus point `t`, the `(a,a)` entry
  of `sigma(t)` is the evaluation of the torus character corresponding to `-r`.

The theorem `SplitPinning.exists_negativeRho_extremalRepresentation` proves
the existence of these witnesses; the primary definition selects them by
classical choice. The record type alone asserts no existence.

The quantifier on `V` is unrestricted: it includes nonaffine, nonreduced, and
empty test schemes. Affine tests used in intermediate steps likewise range over
all commutative `k`-algebras.

The supplied `IsHighestWeight` predicate includes irreducibility, a full torus
weight decomposition, a one-dimensional highest-weight space, and the assertion
that each occurring weight is below the highest weight in the monoid generated
by the simple roots. The implementation uses the latter three properties to
construct the extremal coordinate. The supplied pinning, root datum, full
coroot-span condition, and highest-weight representation remain hypotheses;
this file proves none of their existence. It also supplies no Bruhat covering,
Steinberg irreducibility, or entire covariant-space finite-dimensionality result.

The supporting lemmas and proof route are as follows. The generic theorem
`MatrixRepresentation.pointMatrix_diagonal_of_affineMatrix` evaluates the
diagonal affine formula at the universal affine point, then pulls it back
along an arbitrary test point. Naturality of matrix coefficients and character
evaluation proves the same formula on that original test scheme.
`exists_unique_characterBasis_index` uses the character projector to show
that the highest character occurs among the basis vectors. Its one-dimensional
character space then forces uniqueness by linear independence of the basis.

`SplitPinning.pairing_polarization_rho_pos_of_mem_positiveRootMonoid` proves
that pairing with `nu` is strictly positive on every nonzero element of the
positive simple-root monoid. The proof inducts over its additive closure,
using the proved positivity on simple roots from `CanonicalRhoDynamics` and
additivity. The zero case is retained. Applying this to `r - mu` for every
other occurring weight proves
`SplitPinning.exists_highestWeight_characterBasis`: a character basis has
exactly one coordinate of weight `r`, and every other coordinate has strictly
smaller pairing with `nu`.

The final proof conjugates the whole supplied representation by
`MatrixRepresentation.basisCoordinatePoint b`, where `b` is that character
basis, and then takes its actual dual scheme representation. The conjugated
representation restricts to the diagonal torus-character formula on all affine
tests; the universal-point lemma extends it to all relative tests.
`MatrixRepresentation.dual_pointMatrix_diagonal` proves the dual formula with
negative characters using the inverse-transpose matrix, so `sigma` is an
actual composite of group-scheme morphisms. Its exponents are the pairings
`p.rootDatum.toLinearMap (-mu c) nu`. Negating the strict highest-coordinate
inequality gives the strict minimum, and `mu a = r` identifies its entry with
`-r`. Finally,
`MatrixRepresentation.cocharacter_eq_diagonal_of_pointMatrix` uses all-test
morphism extensionality and the character-cocharacter lattice pairing to
identify the exact diagonal cocharacter.

The provenance is an internal derivation from the existing Library definitions
and proved character-basis, basis-change, dual-representation, integral-rho and
lattice-pairing interfaces. No external source theorem or additional existence
assumption is installed by this contribution.
