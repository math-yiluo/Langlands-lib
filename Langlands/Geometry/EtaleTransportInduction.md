# Exact induction and restriction for actual small-etale transport sheaves

This internal construction extends the existing topological transport induction
method to the actual small-etale transport category of a scheme. Let
`Y : Scheme.{u}`, let `G : Type w` be a group, and let
`ρ : G →* (Aut Y)ᵐᵒᵖ` describe its action with the convention of
`EtaleTransportCategory`. Scheme and group universes are independent. The
module constructions assume `Small.{u} G`, `R : Type u` a commutative ring, and
module carriers in `Type u`. The definitions retain genuine scheme maps and all
group labels, including for nonfaithful actions.

`translateArrows` assigns to each label the costructured arrow given by the
actual translation isomorphism, for left Kan extension along `(inclusion ρ).op`.
`toTranslate` factors every costructured arrow through the translate given by its
label, using `Object.ordinaryPart`. In every such factorization,
`label_eq_of_hom` identifies the label and `factor_left` identifies the actual
underlying scheme map. Arrows between discrete translation labels act as the
identity on the underlying source scheme. These two facts construct a zigzag
between any pair of factorizations and prove `translateArrows_final`. The proof
uses extensionality for actual scheme maps; it does not require scheme hom sets
to be subsingletons. These constructions need no group-smallness hypothesis.

`smallTranslateArrows` shrinks only the labels to `Shrink.{u} G`, giving a
`u`-small final family under the stated smallness assumption. Finality yields
module colimits over each of the potentially large costructured-arrow
categories. Exactness of module coproducts and the final-functor theorem prove
that these colimits preserve finite limits. An explicit pointwise Kan-extension
instance and `inclusionLanEvaluationIso` identify evaluation of the left Kan
extension with the corresponding comma colimit, using the actual site and
coefficient universes. Evaluation then proves
`inclusion_lan_preservesFiniteLimits`.

`induction` is the composite of ordinary sheaf inclusion into presheaves, this
left Kan extension, and the previously constructed transport sheafification.
`inductionAdjunction` is the constructed adjunction to `toSheaf`, the existing
restriction to ordinary small-etale sheaves. Induction preserves finite limits
by the three factors and preserves colimits by the adjunction. These properties
are exposed in `inductionExactFunctor`. Its finite-limit preservation also
implies preservation of monomorphisms; the adjunction therefore proves
`toSheaf_preservesInjectiveObjects`. No injective-preservation result is assumed.

For exactness in the other direction, `isLocallySurjective_restrict` takes
transport-local lifts to ordinary local lifts, directly from the definition of
the transport covering topology. It does not require group smallness. Local
bijectivity detects sheafification on the essentially small affine transport
basis; its cover-dense sheaf equivalence transports this property to the full
transport site. The instance `transport_moduleSheafCompose` uses the existing
corepresentability of module forgetting by the free rank-one module to prove
that forgetting module structure preserves the sheaf condition on this large
site, without a large-limit hypothesis. Mathlib's local-surjectivity criterion
for epimorphisms then proves `toSheaf_preservesEpimorphisms`. Combined with
restriction's existing finite-limit preservation and its additive structure,
this yields preservation of homology and finite colimits.
`toSheafExactFunctor` packages the actual exact restriction functor.

The provenance is internal categorical assembly, rather than a new assertion
attributed to Harris or Berkovich. It reuses `EtaleTransportCategory`,
`EtaleTransportSite`, `EtaleTransportAffine`, `EtaleTransportSections` and
`EtaleTransportAbelian`, and the module corepresentability construction in
`EtaleGodement`. The discrete-family proof follows the published Library's
`EtalePullbackAdjunction` and `Sheaf.Equivariant.Induction`, replacing the
open-set subsingleton argument by the underlying-scheme-map factorization.
`inclusionLanEvaluationIso` adapts the proof of Mathlib's
`CategoryTheory/Functor/Flat.lean`, `lanEvaluationIsoColim`, to independent site
and coefficient universes, as in `EtalePullbackAdjunction.lanEvaluationIso`.
Mathlib supplies exact module coproducts, final-functor transport of exact
colimits, sheafified-Kan adjunctions, dense-subsite transport of local
bijectivity, and the exactness and injective-preservation criteria. The output
here is exact functors between actual sheaf categories. Ordinary derived-section
comparison, smoothness, compact supports, analytic geometry, arithmetic
coefficients, level towers and Harris specialization remain successor work.
