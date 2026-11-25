# Intertwiners to the reversed standard module

Module `Langlands.Representation.Archimedean.RealReverseIntertwinerKernel`.
`realReverseIntertwinerKernel` is in the namespace
`Langlands.Archimedean.RealReverseIntertwinerKernel`; the packaged reduction is in
`Langlands.Archimedean`.

## Purpose and provenance

`realReverseIntertwinerKernel` (and its packaged form `realReverseIntertwinerKernelReduction`)
proves `RealReverseIntertwinerKernelStatement` (Library module
`RealStandardIrreducibleCriterionReduction`) from three inputs passed as hypotheses.
That statement says: for a Langlands-ordered list `ds` of real blocks of rank `n`, every
`(𝔤𝔩_n(ℝ), O(n))`-intertwiner `T` from the `O(n)`-finite standard module of `ds` to that of
`ds.reverse` vanishes on every proper `(𝔤, K)`-submodule `W` (`W ≤ ker T`).

It is one of the three inputs of `realStandardIrreducibleCriterionReduction`, the reduction of the
"if" direction of Speh's irreducibility criterion for `GL_n(ℝ)`.

Context from the literature, which the proof does not use. When every block of `ds` is a
character (the principal-series case), the statement follows from Mœglin, *Representations of
GL(n) over the real field*, PSPM 61, 1997, Theorem 4 (p. 159), together with finite length.
Part (i) says that the unique irreducible quotient of the principal series is isomorphic to the
unique irreducible submodule of the principal series with the characters reversed. Part (ii) says
that this quotient occurs with multiplicity one. For lists that also contain induced `GL_2`
blocks, the corresponding argument needs the general Langlands classification (Mœglin, §10,
Theorem 10a, p. 164, the unique irreducible quotient for general standard data; Knapp,
*Representation theory of semisimple groups*, 1986, Theorem 8.54, p. 267, the Langlands
classification; the paragraph before it realizes the Langlands quotient as the image of the long
intertwining operator into the module induced from the opposite parabolic subgroup) and the
multiplicity-one argument sketched in the Library's `RealStandardIrreducibleCriterionReduction.md`
(description of `RealReverseIntertwinerKernelStatement`). Mœglin's Theorem 10b (p. 164) is Speh's criterion
itself, the result this statement serves.

The proof here instead uses an analytic limit pairing: the asymptotics of matrix coefficients
along the standard parabolic subgroup whose diagonal blocks are the tie classes of `ds` (module
`RealReverseInduced`; compare Knapp 1986, Proposition 8.61, p. 274).

The result is conditional. The three inputs are hypotheses of `realReverseIntertwinerKernel`, and
none is proved here:

- `RealLeviChartIntegrableStatement` (`hT1`, module `RealLeviChartIntegralStatement`). It is proved in the Library as `realLeviChartIntegrable` (module
  `RealLeviChartIntegrable`); this module keeps it as a hypothesis and does not import that proof;
- `RealLeviParabolicIntegrationStatement` (`hT3`, module
  `RealLeviParabolicIntegrationStatement`);
- `RealTemperedStandardIrreducibleStatement` (`htemp`, Library module
  `RealTemperedIrreducibleStatement`): standard modules whose blocks all have the same real
  exponent are irreducible.

The nonvanishing of the limit pairing for the tie data is not an extra input: it is
`realLeviWitness` (Library module `RealLeviWitness`) under `hT1`, used inside
`RealReverseInduced.reverseKernel`.

## Statements

- `realReverseIntertwinerKernel hT1 hT3 htemp : RealReverseIntertwinerKernelStatement`.
- `Langlands.Archimedean.RealReverseIntertwinerKernelReductionStatement` (definition, a `Prop`):

  `RealLeviChartIntegrableStatement → RealLeviParabolicIntegrationStatement →
  RealTemperedStandardIrreducibleStatement → RealReverseIntertwinerKernelStatement`.

  Provenance: derived; it packages the three inputs of `realReverseIntertwinerKernel` as one
  implication.
- `Langlands.Archimedean.realReverseIntertwinerKernelReduction :
  RealReverseIntertwinerKernelReductionStatement`.

## Proof

Notation (modules `RealLeviSlices`, `RealInducedStandardBound`): for
`dss : Fin c → List RealBlock`, `flat dss = dss 0 ++ ⋯ ++ dss (c-1)`, `sz dss i = realRank (dss i)`,
`cls (sz dss) p` is the block containing the position `p : Fin (∑ i, sz dss i)`, `cl dss i` is the
class list `dss i` twisted by `|det|^{shift dss i}`, and `realPositionBlockExponent ds p` is the
real part of the exponent of the block of `ds` containing the position `p`.

Let `n`, `ds`, `T`, `W` satisfy the hypotheses of `RealReverseIntertwinerKernelStatement`.
`RealTieClasses.exists_tieData htemp ds hord` gives classes `dss` with `flat dss = ds` such that

1. `realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p` for all
   positions `p ≤ q` (`hanti`),
2. `realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p` for all
   positions `p, q` with `cls (sz dss) p < cls (sz dss) q` (`hstrict`), and
3. every `(𝔤𝔩_{sz_i}(ℝ), O(sz_i))`-module of `O(sz_i)`-finite functions of
   `realStandardModule (sz dss i) (cl dss i)` is irreducible (`hX`).

`realRank_flat` gives `n = realRank ds = ∑ i, sz dss i`, so `n` is replaced by `∑ i, sz dss i`.
Then `RealReverseInduced.reverseKernel hT1 hT3 hanti hstrict hX` applies and gives `W ≤ ker T`.
Inside `reverseKernel`, the nonvanishing of the limit pairing comes from
`realLeviWitness hT1` under conditions 1–3.
`realReverseIntertwinerKernelReduction` is `realReverseIntertwinerKernel` with its three
hypotheses taken as the premises of the implication.
