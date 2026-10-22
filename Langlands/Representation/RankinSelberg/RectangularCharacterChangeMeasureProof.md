# The JPSS rectangular character-change Haar law

Author: Worker 90.

This proof unit proves the existing, unchanged proposition
`Langlands.RankinSelberg.CharacterChangeRectangularMeasureStatement.{uF}`.
The field-carrier universe `uF` remains arbitrary. The public theorem
`characterChangeRectangularMeasureStatement` has exactly that type, with the
general Haar component first and the product component second. The two
components are also exposed as `characterChangeRectangularHaarStatement` and
`characterChangeRectangularProductStatement`, in the same namespace.

## Internal provenance

This is a derived specialization of the published theorem
`Langlands.HarmonicAnalysis.padicRectangularHaarScaling` in
`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` (Worker 110), applied
to the existing JPSS objects in `CharacterChangeBlocks` and
`UnequalRankCharacterIntegrals`. The target pair was supplied by Worker 99 in
`RectangularCharacterChangeMeasureStatement`. The proof imports both published
modules and changes none of their definitions, statements, or imported files.
It requires no new literature assertion or independent Haar normalization.

## The matrix and determinant calculation

The private construction `characterChangeRowDiagonal a j` is an actual element
of `GeneralLinear j F` with diagonal entries

```text
A[i,i] = ((a^(i.val+1))^(-1) : F).
```

Its inverse has diagonal entries `a^(i.val+1)`. The two matrix inverse laws
follow from diagonal multiplication and the unit inverse laws. The private
theorem `characterChangeRowDiagonal_mul` uses `Matrix.diagonal_mul` entrywise to
identify the function `X ↦ A * X` with the existing linear equivalence
`characterChangeRectangular a j n`, on precisely `j` by `n+1` matrices.

Write `S = ∑ i : Fin j, (i.val+1)`. The private determinant lemma proves the
unit-valued identity

```text
GeneralLinear.determinant A = (a^S)^(-1).
```

The proof applies unit extensionality, the determinant formula for a diagonal,
the product-of-inverses identity, and the product-of-powers identity. Thus it
checks the actual determinant of the actual matrix used in the measure theorem.

## Normalization and the pushforward sign

The private modulus lemma applies `T.normalizedAbsUnits` to this determinant.
The character and its value agree with the published
`normalizedAbsoluteValue T`, namely the residue-cardinality-normalized absolute
value `T.normalizedAbs`. No base-field spectral norm is substituted.

Specializing `padicRectangularHaarScaling F T j (n+1) ν A 1` gives the factor

```text
(|det A|^(n+1) / |det 1|^j)^(-1)
  = (((|a|^S)^(-1))^(n+1))^(-1)
  = |a|^((n+1)*S).
```

The implementation simplifies the identity matrix, uses the monoid character's
inverse and power laws, cancels the two inversions, and commutes the natural
exponent factors. Nonnegative-real extensionality identifies the result with
exactly `characterChangeRectangularModulus (normalizedAbsoluteValue T) a j n`.
The sign is positive because the supplied Haar theorem uses the inverse
Jacobian for pushforward, while the row matrix itself has negative powers.
The general theorem's nonnegative-real scalar action on measures is
definitionally the extended-nonnegative-real coercion action used by the
published measure-law predicate.

The public general proof keeps every quantifier of
`CharacterChangeRectangularHaarStatement`: every prime, p-adic field, supplied
topological realization, natural dimensions, Borel measurable structure on the
matrix space, additive Haar measure, and field unit. It installs only the
supplied topology before applying the general rectangular theorem; no extra
measure or topology assumptions are introduced.

## The existing product measure and boundary cases

The product proof installs the exact scalar structures from the product target:
`T.topology`, `T.valuativeRel`, `T.localField`, `T.secondCountableTopology`, the
scalar Borel measurable space, and its reflexive `BorelSpace` instance. It also
installs the proved `T.sigmaCompactSpace`. The scalar Haar bundle supplies
`η.measure.IsAddHaarMeasure`; its local finiteness and the field's countability
properties give sigma finiteness by the existing instances. Topological
addition with the scalar Borel structure supplies measurable addition, and
second countability makes the finite nested products Borel. The existing
`rectangularMeasure_isAddHaar` instance therefore applies to

```text
rectangularMeasure η j (n+1)
  = Measure.pi (fun _ : Fin j =>
      Measure.pi (fun _ : Fin (n+1) => η.measure)).
```

The proof directly applies the general component to this measure. It makes no
choice of scalar mass, no self-duality assumption, and no replacement of the
existing JPSS product measure.

All arguments include `j=0`: the diagonal is the empty invertible matrix, its
determinant is one, the exponent sum is zero, and the modulus is one. For the
product, the existing `rectangularMeasure_zero_rows` identity identifies the
measure with the unit point mass `Measure.dirac 0`; no separate branch is needed
in this proof. At `n=0` there is one column and the same formulas apply.

These theorems discharge the rectangular measure-law hypothesis of the
unequal-rank transport consumers. The separate quotient measure law and the
other hypotheses of those consumers are outside this proof unit.
