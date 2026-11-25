# Same-level cuspidal preimages: the VIII.5 inclusion from VIII.4.2

Waldspurger (2003), VIII.5, printed p.332 (PDF p.98), proves
Theorem VIII.1.2 from the inclusion
`⊕_{ω ∈ E₂(G)^H_χ} A(ω)^{H×H} ⊂ p_χ(°C_H)`, which it justifies by
Theorem VIII.4.2 "and since `p_χ` is `G × G`-invariant". The published
target `RationalCuspidalFixedCoefficientLiftingStatement` (module
`RationalCuspidalCentralStatements`) is that inclusion on the actual
interfaces. This module proves it from two named closed propositions,
which are not proved here:

- `RationalSchwartzCentralConvergenceStatement.{u}`
  (`RationalCuspidalConvergenceStatements`): absolute convergence of the
  actual central integral for every actual Schwartz function;
- `RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u,uV}`
  (`RationalCuspidalLowerInclusionStatement`): the inclusion
  `A₂(G)_χ ⊆ p_χ(°C(G))` from the first paragraph of the proof of
  Theorem VIII.4.2 (printed p.330, PDF p.96), at carrier universe `uV`.

The averaging that implements "`p_χ` is `G × G`-invariant" is the generic
theorem `exists_biInvariant_central_preimage` of
`SchwartzCompactLifting`. It averages a preimage over `H × H` in the
two-sided translation representation on a translation-stable Schwartz
subspace. This module supplies its hypotheses for the actual cuspidal
space.

## Generic lemma

`CentralIntegralConvergesOn.mono`: convergence of the central integral on
a Schwartz subspace `E` gives convergence on every `E' ≤ E`. The proof
applies the hypothesis to the same function.

## The actual cuspidal space

The variables are the actual structural choices of the targets: a
nonarchimedean local field `F`, `G` affine of locally finite type, a
compact open `K` with the minimal Iwasawa pair for `(i, ν)`, and a matrix
representation `ρ` on `Fin N`. No reductivity, torus or closedness
hypothesis is needed for the lemmas below.

- `rationalCuspidalSubmodule_isTranslationStable`: the actual cuspidal
  kernel `rationalCuspidalSubmodule hKc hPK ρ` is stable under
  `Space.translate` for the published actual weights
  `rationalTranslationWeights K.isOpen hKc hPK ρ` (Waldspurger II.1.2 and
  the height bound). Each defining condition, the all-translates
  integrable cuspidality `IsIntegrableUnipotentCuspidal` along a proper
  standard unipotent subgroup for a Haar measure, is preserved by
  `IsIntegrableUnipotentCuspidal.translate` from `SchwartzCompactLifting`.
- `mem_rationalCuspidalCentralLevelImage_of_biInvariant`: given a split
  component `s`, any measure `muA` on its point image, any character `χ`
  and convergence `CentralIntegralConvergesOn` on the actual cuspidal
  space, every `H`-bi-invariant element of the raw image
  `rationalCuspidalCentralImage` lies in the raw level image
  `rationalCuspidalCentralLevelImage` at the same compact open `H`. The
  proof gives the group a compact open subgroup from `K`, applies
  `exists_biInvariant_central_preimage` with the weights above, the
  stability lemma and centrality of the split-component image
  (`hs.isCentralSplitTorus.isCentral.range_le_center`). It reads off
  membership in `rationalCuspidalLevel` (cuspidal and `H`-bi-invariant).
- `isBiInvariant_of_mem_rationalCuspidalCentralLevelImage`: conversely,
  every element of the raw level image at a subgroup `H` is
  `H`-bi-invariant. No convergence is needed. The proof applies the
  published `IsBiInvariant.centralProjection` to the bi-invariant preimage.
- `rationalCuspidalCentralLevelImage_eq_inter_biInvariant`: under the same
  convergence hypothesis and for compact open `H`, the raw level image
  equals the set of `H`-bi-invariant elements of the raw full image. It
  combines the two previous lemmas with the published
  `rationalCuspidalCentralLevelImage_subset`.

## Reduction of the lifting target

`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.fixedCoefficientLifting`
assumes `RationalSchwartzCentralConvergenceStatement.{u}` and
`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u,uV}` and
proves `RationalCuspidalFixedCoefficientLiftingStatement.{u,uV}`, with the
same independent universes. After introducing all binders of the target,
the convergence statement on the whole Schwartz space (`⊤`) is restricted
to the cuspidal submodule by `CentralIntegralConvergesOn.mono`. For a class
`ω` in `discreteSeriesCentralFixed` at `H` and an `H`-bi-invariant
coefficient `f` of `ω.val.out`, the published consequence
`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.coefficient_mem`
places `f` in the raw full image. Then
`mem_rationalCuspidalCentralLevelImage_of_biInvariant` gives a cuspidal
preimage at level `H`. The Haar measure `mu` on the quotient enters only
through the lower inclusion. The measure `muA` and the character `χ` are
those of the target.

`RationalCuspidalFixedCoefficientLiftingReductionStatement.{u,uV}` records
this implication as a proposition:
`RationalSchwartzCentralConvergenceStatement.{u} →
RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u,uV} →
RationalCuspidalFixedCoefficientLiftingStatement.{u,uV}`.
`rationalCuspidalFixedCoefficientLiftingReduction` proves it by the
preceding theorem. It is an internal conditional reduction. It neither
proves the lifting target nor adds a hypothesis to it. A closed proof of
the target follows by applying it to closed proofs of the two inputs
(convergence is proved as `rationalSchwartzCentralConvergence`; the lower
inclusion `RationalCuspidalDiscreteCoefficientLowerInclusionStatement` is not proved
unconditionally in the Library).
