# Measures on actual rational-point discrete-series twist orbits

Author: Worker 200.

This derived adapter specializes `DiscreteSeriesOrbitMeasure` to the shared
actual rational-point group, its canonical topology and every rational norm
character. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), VI.3, printed p.302 (PDF p.68), equips each
unitary unramified twist orbit with the measure locally preserved by its
character parameterization. Its character measure has already been fixed
in I.1, printed p.239 (PDF p.5), through restriction to split-center
characters. Registered source: `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The reciprocal-fiber formula and its specialization below are internal
construction laws implementing the VI.3 convention relative to a supplied
character measure.

## Actual data and retained hypotheses

The field `F : Type u` has the existing `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances, without a
characteristic restriction. The shared `GroupScheme G` is affine and locally
of finite type. Its rational points use `rationalPointTopology F G.X`, and
`rationalPoints_nonarchimedeanGroup` supplies the open-subgroup basis in
that topology. The representation universe `uV` is independent of `u`.

Let `T` be an affine commutative group scheme and `s : T.toGrp ⟶ G` an
actual morphism with `hs : GroupScheme.IsCentral s`. The central subgroup
is the actual point-map range `A = s(T(F))`; normality follows from
`hs.range_le_center` before binding the dependent quotient Haar instance
and discrete-series class. Give `G(F) / A` a measurable space and a Haar
measure `mu`. The classes are the existing `DiscreteSeriesClass A hA mu`
on the canonical smooth-representation framework. Its intended source
specialization takes `s` to be the actual split-component inclusion.

Every declaration retains
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`. This concerns
the image of the actual point map followed by the actual rational-character
valuation map. `finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega`
derives finiteness of the actual unitary twist stabilizer. Stabilizer
finiteness is thus a proved consequence of the displayed premise, not an
additional representation-theoretic input.

The underlying conditional central-quotient argument is the deduction in
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
edition, V.2.6, printed p.108 (PDF p.114), registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard proves the preceding actual-image finite-index lemma within the
book. This adapter preserves that lemma as a separate proof obligation;
it does not reclassify it as an allowed permanent structural hypothesis
for completing the Plancherel program.

## Measure and construction laws

The character family is exactly
`nu = fun psi => (rationalNormCharacters G psi).toMul`.
Its existing unitary unramified character group has the Borel sets of the
compact-open topology. The orbit has the Borel sets of its existing
stabilizer-quotient topology. These are the instances from
`DiscreteSeriesOrbitMeasure`, specialized without changing the spaces.

Let `omega` be the base class, `S` its actual unitary stabilizer and
`p = discreteSeriesOrbitMap A hA mu nu omega` the actual twisting map.
For a supplied measure `lambda` on the character group,
`rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda` is the
existing generic measure, with the finite instance just derived. Hence

\[
  d\eta = |S|^{-1}\,p_*\lambda.
\]

`rationalDiscreteSeriesOrbitMeasure_apply` evaluates each measurable orbit
set `E` as `|S|⁻¹ * lambda (p ⁻¹' E)`.
`rationalDiscreteSeriesOrbitMeasure_univ` gives total mass
`|S|⁻¹ * lambda univ`. `rationalDiscreteSeriesOrbitMeasure_smul` proves
compatibility with every extended nonnegative scalar. Their implemented
proofs install the same derived finite instance and apply the corresponding
generic construction laws; the specialized measure unfolds to that generic
measure. No invariance of `lambda` is needed for these laws.

`lintegral_rationalDiscreteSeriesOrbitMeasure` specializes the nonnegative
pushforward formula: for every measurable `f` with values in the extended
nonnegative reals,

\[
  \int_{\mathcal O} f(\eta)\,d\eta
    = |S|^{-1}\int_{\operatorname{Im}X(G)}f(p(\chi))\,d\lambda(\chi).
\]

Infinite values are allowed. This is a nonnegative integration statement;
complex integral convergence remains a separate obligation.

## Local preservation and independence of the base class

`isLocallyMeasurePreserving_rationalDiscreteSeriesOrbitMap` additionally
assumes `Measure.IsMulLeftInvariant lambda`. It proves local preservation
for the actual rational-point twisting map: every character lies in an
open injectivity chart, every measurable subset of that chart has a
measurable image, and the image's orbit measure equals its character
measure. The proof derives the finite stabilizer and invokes the generic
local-preservation theorem. That theorem uses the actual orbit
homeomorphism and the disjoint-translate proof for finite character
quotients. Local preservation itself is never supplied as an input.

`map_rationalDiscreteSeriesOrbitMeasure_baseChange` uses the same invariant
`lambda` at `omega` and `chi • omega`. It derives finite stabilizers for
both actual base classes, then applies the existing measure comparison.
The homeomorphism `discreteSeriesOrbitBaseChange` is the identity on
represented classes, and its pushforward of the measure at `chi • omega`
is the measure at `omega`. The underlying generic proof commutes twists,
identifies the stabilizers and cancels character translation by left
invariance.

## Remaining source realization

The construction retains a supplied character measure and its scale.
Waldspurger I.1 normalizes Haar measure to mass one on `Im X(A_G)`, then
fixes the measure on `Im X(G)` by local preservation of actual restriction.
It does not normalize the latter character group to mass one. Constructing
that restriction normalization, its surjectivity and covering comparison
remain separate obligations. This adapter also leaves the actual
split-component construction, the finite-index proof and comparison of
image rank with split-center dimension to their respective realizations.
The conclusions apply conditionally to the displayed actual data, even
without connectedness or reductivity; they do not assert an unconditional
realization for every reductive group. Smooth coefficient families,
formal degrees, complex convergence, wave packets, spectral finiteness,
inversion and Plancherel are outside this pair.
