# Discrete-series orbit measures with the I.1 character scale

Author: Worker 200.

This derived adapter combines the existing actual character Haar measure
with the existing actual discrete-series orbit measure. It implements the
measure conventions in Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), I.1, printed p.239
(PDF p.5), and VI.3, printed p.302 (PDF p.68). I.1 assigns probability
Haar measure to the split-component character group and requires
restriction from the group's character group to preserve measure locally.
VI.3 requires the character-to-twist-orbit map to preserve measure locally.
The formulas below are internal consequences of those existing
constructions, rather than formulas explicitly printed in the article.

## Actual data and retained hypotheses

The local field `F : Type u` has the shared
`IsNonarchimedeanLocalField` structure. The group scheme `G` is affine
and locally of finite type. Its actual rational points use
`rationalPointTopology F G.X` and the proved nonarchimedean-group
instance. The representation universe `uV` is independent of `u`.
There is no restriction on characteristic, and no split or quasisplit
assumption on `G`.

Let `T` be an affine commutative group scheme,
`s : T.toGrp ⟶ G` an actual morphism, and
`hs : GroupScheme.IsCentral s`. Put `A = s(T(F))`. Its normality is
derived from `hs.range_le_center` before the quotient Haar measure and
discrete-series class are bound. The quotient `G(F) / A` carries the
displayed measurable space and Haar measure `mu`. All classes and twists
are the existing canonical smooth-representation objects.

The premise
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`
concerns the actual central valuation image. The imported
`finite_rationalUnitaryUnramifiedCharacterRestrict_ker` and
`finite_rationalDiscreteSeriesStabilizer` derive finiteness of the actual
restriction kernel and unitary twist stabilizer from this premise.
Neither finiteness nor local measure preservation is an additional input.
The actual-image finite-index assertion remains a separate proof
obligation. It is an in-book deduction in Renard V.2.6, not a permitted
permanent external structural assumption for completion of the program.

The source specialization takes `s` to be an actual split-component
inclusion for a connected reductive `G`. The construction laws below also
hold for the more general displayed central data. For the source's I.1
restriction comparison, `T` must additionally be locally of finite type;
the imported
`isLocallyMeasurePreserving_rationalUnitaryUnramifiedCharacterRestrict`
then uses connected reductivity and `GroupScheme.IsSplitComponent s`.

## Fixed scale and construction laws

Write `C` for the existing actual unitary unramified character group for
the family `fun psi => (rationalNormCharacters G psi).toMul`. It carries
its compact-open topology and Borel measurable space. Write `h_G` for
`rationalUnitaryUnramifiedProbabilityHaar G`, `K` for the kernel of
`rationalUnitaryUnramifiedCharacterRestrict s`, and
`lambda_s = rationalUnitaryUnramifiedCharacterHaar s hs hindex`.
The imported character construction proves

\[
  \lambda_s=|K|\,h_G.
\]

For a base class `omega`, write `S` for
`discreteSeriesStabilizer A hs.range_le_center mu nu omega` and `p` for
the existing actual `discreteSeriesOrbitMap`. The orbit carries the
Borel measurable space of its existing stabilizer-quotient topology.
The new definition is precisely

\[
 \eta_\omega
 = \operatorname{rationalNormalizedDiscreteSeriesOrbitMeasure}
       (s,hs,\mu,hindex,\omega)
 = |S|^{-1}p_*\lambda_s.
\]

It has no supplied character-measure parameter.
`rationalNormalizedDiscreteSeriesOrbitMeasure_eq_smul_probability`
proves that it is `|K|` times the orbit measure constructed from `h_G`,
by the existing character-scale equality and orbit scaling law.
For every measurable orbit set `E`,
`rationalNormalizedDiscreteSeriesOrbitMeasure_apply` proves

\[
  \eta_\omega(E)=\frac{|K|}{|S|}\,h_G(p^{-1}(E)).
\]

Its proof applies the existing orbit-set formula, substitutes the
character-set formula, and commutes the finite scalar factors.
`rationalNormalizedDiscreteSeriesOrbitMeasure_univ` consequently gives
total mass `|K| / |S|`. In particular, the definition does not impose
probability normalization on this orbit.

## Local preservation and independence of the base class

`isLocallyMeasurePreserving_rationalNormalizedDiscreteSeriesOrbitMap`
proves local measure preservation from `lambda_s` to `eta_omega`.
The character measure's Haar instance supplies left invariance, and the
existing rational orbit theorem derives the finite stabilizer and
provides the open injectivity charts, measurable chart images and
measure equalities. No invariance premise needs to be supplied.

`map_rationalNormalizedDiscreteSeriesOrbitMeasure_baseChange` states
that the existing identity-on-classes homeomorphism from the orbit based
at `chi • omega` to the orbit based at `omega` pushes its measure to
`eta_omega`. It applies the existing rational comparison with the same
fixed Haar measure on both sides. The underlying proof commutes twists,
identifies their stabilizers, and uses left invariance to remove
character translation. Thus the measure is independent of the chosen
base class within the actual twist orbit.

## Nonnegative integration

For every measurable extended nonnegative function `f` on the orbit,
`lintegral_rationalNormalizedDiscreteSeriesOrbitMeasure` proves

\[
  \int f\,d\eta_\omega
    = |S|^{-1}\int_C f(p(\chi))\,d\lambda_s(\chi).
\]

The proof specializes the existing rational orbit integration formula.
`lintegral_rationalNormalizedDiscreteSeriesOrbitMeasure_probability`
substitutes `lambda_s = |K| h_G` and uses nonnegative integration against
a scaled measure to prove

\[
  \int f\,d\eta_\omega
    = \frac{|K|}{|S|}\int_C f(p(\chi))\,dh_G(\chi).
\]

Both statements allow infinite integrals. They assert no convergence of
complex integrals.

## Scope and provenance

The imported character Haar construction proves the I.1 local
restriction convention for actual split components under connected
reductivity and the displayed finite-index premise. The present pair
uses that same source measure for VI.3, eliminating the previously free
character scale. Its proofs specialize existing constructions and their
proved laws; it introduces no new analytic or representation-theoretic
input.

This pair does not discharge actual-image finite index, construct a
split component, compare image rank to split-center dimension, or prove
coefficient identities, formal-degree formulas, smooth families, wave
packets, spectral finiteness, inversion or Plancherel.
