# The I.1 Haar measure on actual unitary unramified characters

This derived adapter implements Waldspurger, *La formule de Plancherel pour
les groupes p-adiques* (2003), I.1, printed p.239 (PDF p.5). The source fixes
probability Haar measure on \(\operatorname{Im}X(A_G)\) and then fixes Haar
measure on \(\operatorname{Im}X(G)\) by requiring restriction to preserve
measures locally. The adapter applies the existing finite-kernel Haar
construction to the existing actual rational-point restriction map.

## Actual objects and explicit hypotheses

The field \(F\) has the project's `IsNonarchimedeanLocalField` structure,
in an arbitrary universe. The shared `GroupScheme` \(G\) is affine and locally of finite type over
\(F\). The `CommGroupScheme` \(T\) is affine; the two final restriction
laws additionally require it to be locally of finite type.
Their point groups use the canonical `rationalPointTopology`; their actual
unitary unramified character groups use the existing compact-open subspace
topologies and Borel measurable spaces. Compactness follows from
`compactSpace_rationalUnitaryUnramifiedCharacters`, without a rank premise.

`rationalUnitaryUnramifiedProbabilityHaar G` is probability Haar measure on
this actual compact character group. Its Haar and probability instances and
its total-mass law are supplied.

For a central morphism \(s:T\to G\),
`rationalUnitaryUnramifiedCharacterHaar s hs hindex` is
\[
  \lambda_s=|\ker r_s|\,h_G,
  \qquad
  r_s=\texttt{rationalUnitaryUnramifiedCharacterRestrict s},
\]
where \(h_G\) is `rationalUnitaryUnramifiedProbabilityHaar G`. The premise
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex` concerns the
actual image of the split-component points under the integer valuation map.
It is retained explicitly. It is not finite index of algebraic-character
restriction, and is not proved by this adapter.

The existing `finite_rationalUnitaryUnramifiedCharacterRestrict_ker` derives
finiteness of the actual restriction kernel from centrality and `hindex`.
The generic `restrictionNormalizedHaar` then supplies the displayed measure.
The kernel is nonempty, so its finite cardinality is positive. Thus this
measure is Haar. The equality with the scaled probability measure, its
evaluation on every set, and its total mass \(|\ker r_s|\) are proved.
These constructions do not require connected reductivity or a split-component
premise.

## Restriction laws and implemented proof

The final two theorems additionally assume
`hG : GroupScheme.IsConnectedReductive G` and
`hs : GroupScheme.IsSplitComponent s`. They use
`rationalUnitaryUnramifiedCharacterRestrict_surjective s hG hs`, whose proof
extends circle-valued characters along the injective actual valuation-image
map. Restriction surjectivity is a proved consequence of these actual
algebraic hypotheses, not an additional premise.

`map_rationalUnitaryUnramifiedCharacterHaar` specializes
`map_restrictionNormalizedHaar` to prove the global formula
\[
  (r_s)_*\lambda_s=|\ker r_s|\,h_T.
\]
Here \(h_T\) is probability Haar measure on the actual character group of
\(T\). The kernel-cardinality factor is the total covering multiplicity.

`isLocallyMeasurePreserving_rationalUnitaryUnramifiedCharacterRestrict`
specializes
`isLocallyMeasurePreserving_restrictionNormalizedHaar` to prove that
restriction locally preserves \(\lambda_s\) and \(h_T\). That generic proof
uses the actual quotient by the finite kernel, its homeomorphism to the
target, and reciprocal-cardinality quotient measure. It supplies the open
injectivity charts and the measurable-set identities of
`IsLocallyMeasurePreserving`; this local property is not assumed.

## Scope

This is a conditional actual rational-point realization of the I.1 measure
convention. The remaining actual-image finite-index assertion must be
discharged by its structural owner before removing `hindex`. There is no
characteristic-zero, split-group, quasisplit-group or rank assumption.

The pair fixes character measures, but does not yet specialize the
discrete-series orbit measure to this fixed source scale. It does not prove
complex convergence, character-image rank comparisons, real-part descent,
complex periods, coefficient identities, wave-packet estimates, spectral
finiteness, inversion or the Plancherel theorem.
