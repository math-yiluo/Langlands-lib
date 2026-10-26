# Concrete rank-one extension data for JPSS Lemma 5.5

This module supplies definitions and elementary coordinate formulas for the early
compact-section and scalar Fourier-cutoff argument. It proves no compact-section
existence, Whittaker integral identity, Fourier smoothing identity, zeta comparison
or divisibility statement.

The original source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`: Section 3.1,
printed pages 404–405 (PDF pages 39–40), and Lemma 5.5 with its argument, printed
pages 423–427 (PDF pages 58–62). Printed page 425 uses the complementary cell
`[I, y; 0, 1]` for the compact section. Printed pages 426–427 use the embedded
lower block `[m, 0; x, a]` and scalar smearing to produce the scalar Fourier
factor. No errata for this source were available in the project or Library
errata directories when these definitions were prepared.

## Induction and tensor normalization

`rankOneExtensionLowerModel F t χ σ` specializes the published
`rankOneExtensionLowerInduced` to the exact `rankOneExtensionCharacter F χ`.
It is the actual canonical normalized opposite-parabolic induction, with
covariance by the opposite half modulus and right translation of functions.
Its shape is the reversal of the upper blocks of sizes `1, t+1`, and its ambient
group is exactly `GL_(1+(t+1))`. The ordered lower factors are `σ, χLift`.
The character acts on `ULift.{uW} ℂ` by conjugation through
`ULift.moduleEquiv`, exactly as in the published divisibility target.
The field and representation universes remain independent. No smoothness,
irreducibility or unitary hypothesis is imposed on `σ` or on the arbitrary
quasicharacter `χ` by these definitions.

`rankOneExtensionLowerSection` is the actual smooth covariant-function carrier
of that representation, and `rankOneExtensionLowerSectionEval` uses the existing
`Induction.eval`. It returns the published reversed finite tensor carrier,
named `rankOneExtensionLowerTensor`. `rankOneExtensionLowerPureTensor w z`
reindexes the existing pure tensor for `(z,w)` by `Fin.revPerm`.
`rankOneExtensionTensorContraction ℓ` reverses that reindexing and uses the
existing `Shahidi.pairFunctional` with `ULift.moduleEquiv` and `ℓ`.
Consequently its value on that pure tensor is exactly `ℓ(w) * z.down`, without
any modulus, character or Haar scalar. `rankOneExtensionWhittakerContraction`
specializes to a supplied member of `Whittaker.glInverseFunctionals ψ t σ`.
`rankOneExtensionLowerSectionCoefficient` composes evaluation and contraction;
it does not claim this coefficient satisfies a Whittaker transformation law.

## Coordinates and Fourier sign

The coordinates start on `Fin (t+1) ⊕ Fin 1`. The explicit equivalence
`rankOneExtensionCellCoordinates` first concatenates these coordinates and
then casts the rank `(t+1)+1` to `1+(t+1)`. Thus the large block comes first and
the scalar coordinate has zero-based index `t+1`; no equality of these two rank
expressions is implicit. `rankOneExtensionHeadIndex` and
`rankOneExtensionScalarIndex` name the corresponding indices.

`rankOneExtensionUpperCell t y` is the actual unit `[I,y;0,1]`, constructed with
inverse `[I,-y;0,1]`. `rankOneExtensionLowerBlock t m x a` is the actual unit
`[m,0;x,a]`, constructed from its nonzero determinant `det(m)*a`.
The row `x` is not scaled by `m` or `a`. The two `_apply` lemmas expose the full
block matrices at the explicit coordinate indices.

`rankOneExtensionEmbeddedLowerBlock t k m x a` uses the existing `rankInclusion`
to append an identity of rank `k+1`, hence always a positive trailing rank.
`rankOneExtensionFirstTrailingIndex` is its first trailing coordinate,
with zero-based index `t+2`. `rankOneExtensionSmearingUnipotent t k u`
is the actual transvection `I + u E_(t+1,t+2)`, with inverse obtained by replacing
`u` by `-u`. Its entry formula exposes its unique off-diagonal coordinate.
The elementary multiplication lemma
`rankOneExtensionEmbeddedLowerBlock_mul_smearing_pairing` computes the
scalar-row/first-trailing-column entry after right multiplication as `a*u`.
This is the plus-sign pairing compatible with the published scalar
`HarmonicAnalysis.fourierIntegral`; no Fourier identity is proved here.

These names and the explicit rank cast are implementation choices derived from
the original block formulas. The coordinate constructions work over every field.
For future analytic statements the cell variable uses the existing
`HarmonicAnalysis.rowMeasure μ (t+1)`, row variables use that same product
measure (or the existing `rectangularMeasure μ 1 (t+1)` when represented as a
matrix), and scalar smearing uses the supplied scalar Haar `μ.measure`.
There is no new measure or independent normalization in this module.
Future comparison statements must retain the source's rank restrictions and
the common trailing block; these definitions alone do not supply them.
