# Compact pushforwards for twisted character regularity

This module proves the geometric premise
`TwistedCharacterRegularValuesGeometryStatement` of the Library's reduction
`twistedCharacterRegularValuesReduction`, from the additive submersion principle
`HarmonicAnalysis.CompactSubmersionPushforwardStatement`:

- `twistedCharacterRegularValuesGeometry_of_compactSubmersion` derives the
  geometry statement from the pushforward statement, and
- `twistedCharacterRegularValues_of_compactSubmersion` composes it with the
  reduction and so derives `TwistedCharacterRegularValuesStatement` from the
  pushforward statement.

`Langlands.BaseChange.TwistedCharacterRegularValues` applies the second theorem to
`HarmonicAnalysis.compactSubmersionPushforward`, which proves the pushforward
statement.

**The witnesses.** Fix `F`, a cyclic `F`-algebra `E` for `σ` of order `l` and a
σ-regular `δ ∈ GL_n(E)`. The cyclic algebra hypothesis supplies that `E` is
finite and reduced and that `σ^l = 1`. `GeneralLinear.finiteAlgebraUpperTriangularCartan`
gives a compact open subgroup `K` and representatives `M` with Cartan coverage
and uniform contraction of compact open subgroups of the upper triangular
subgroup `P`. These are the first two witnesses.

**Local constancy of the pushforward.** Fix a compact open subgroup `L` of `P`.
The matrix Haar chart `compactMatrixHaarChart` embeds `K × L` openly into the
product of the full and upper triangular matrix algebras.
`exists_normalizedHaar_matrix_chartDensity` gives a locally constant density `f`
with compact support equal to the image of the chart, whose density measure
against an additive Haar measure is the image of the product of the normalized
Haar measures of `K` and `L`. The image is open because the chart is an open
embedding and closed because `K × L` is compact.

The coordinate twisted product `twistedConjugationMatrixMap σ`, which sends
`(y, k, p)` to `k y σ(k)⁻¹ σ(p)`, is extended by zero outside this image in the
source variables. The extended map `Φ` is continuous on the whole product (it is
continuous on the clopen image by `twistedConjugationMatrixMap_continuousOn`) and
agrees with the coordinate map near every point of the image. At each point of
the support of `f`, `twistedConjugationMatrixSubmersion` gives a joint strict
derivative of the coordinate map at `(δ, k, p)` that is onto in the source
directions; local agreement transfers it to `Φ`. The norms are the
finite-algebra norms of `finiteAlgebraNormedRing` on the matrix algebra over the
normed local field `F`, with the induced norm on the upper triangular
subalgebra; these are ultrametric and proper, as the pushforward statement
requires.

The pushforward statement then gives an open set `U` of parameter matrices
containing `δ` on which the pushforward of `f` times Haar measure under
`Φ(y, ·)` does not depend on `y`. Composing the chart with the coordinate map
gives the group twisted product `twistedConjugationProductMap` followed by taking
the matrix (`twistedConjugationMatrixMap_units`). Taking the matrix of a unit is
a measurable embedding, so the group pushforwards
`twistedConjugationPushforward` at `y` and at `δ` agree for every `y` whose matrix
lies in `U`. This is `HasLocallyConstantTwistedConjugationPushforward`, the third
witness.

This is the twisted, additive-coordinate form of Harish-Chandra's §3, Lemma 1,
in *A submersion principle and its applications* (1981, printed pp. 97–98,
source `harish-chandra-1981-submersion-principle`): there the map
`(y, x, p) ↦ (y, x y x⁻¹ p)` is submersive, so the functions `f_{α,y}` defined by
pushforward are locally constant in the regular parameter `y`.
