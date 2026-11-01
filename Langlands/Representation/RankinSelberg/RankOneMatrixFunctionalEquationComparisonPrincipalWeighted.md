# Spectral weights in principal compact-measure extraction

This internal derived prerequisite extends `principalMeasure_extraction` from
`RankOneMatrixFunctionalEquationComparisonPrincipalAverage` to the actual
Godement–Jacquet matrix integrand at every complex exponent. It introduces no
new measure or normalization. The definition `principalWeightedScalarAverage`
is the scalar function displayed below, using the existing principal measure
and the actual determinant weight.

For a canonical p-adic field, a nontrivial unitary additive character with
conductor `c`, and a positive principal level `a` with `c + a ≥ 0`, use the
same matrix test `boxLatticeTest F (c+a) c a` and compact principal measure
`principalAveragingMeasure F a C`, where `C` is the positive
`boxExtractionConstant F (c+a) c a`. For every continuous standard-character
equivariant function `W`, actual convergence of its matrix integral at `s`
implies actual convergence of

```text
g ↦ (∫ k, W(rankOneEmbedding g · k) dμ) · |det g|^s
```

against the existing weighted `glOneMeasure`. The two integral values are
equal. The choices of test, measure, and constant are independent of `W`
and `s`.

The proof multiplies `W` by the determinant weight, whose continuity is
already proved in `RankOneMatrixWhittakerComparisonBox`. The determinant of
an upper unipotent matrix is one, so this multiplication preserves the
standard character. It applies the raw-function principal extraction and
then factors the determinant weight out of the compact average: almost every
principal parameter has determinant norm one, and the rank-one embedding
preserves the determinant. These are actual support and matrix identities;
the principal parameters are not asserted to have determinant equal to one.

The module also records these weight identities separately. Factoring out a
weight is an equality of totalized Bochner integrals, while
`principalMeasure_weighted_extraction` explicitly retains the convergence
conclusion furnished by the original extraction. No converse convergence
claim is made. No representation, bi-smooth realization, Fourier partner,
self-duality, or functional equation is assumed or proved here.
