# Restriction of the projective degree-one comparison

This module is derived infrastructure for the projective frame bundle. Its
inputs are the actual degree-one bundle and overlap comparisons constructed in
`ProjectiveBundle/Tautological`, the canonical pullback comparisons in
`Modules/RefinedPullbackComparison`, and the transport law in
`Modules/CommonSourceTransitionTransport`. No external source assertion is used.

For a scheme `S` in any common universe, a module sheaf `M` on `S`, a natural
number `n`, and an explicit proof `hM` that `M` is locally free of rank `n + 1`,
the projective frame bundle has chart maps
`chart hM U : P^n_U → frameBundle M n hM`. Its actual global line bundle is
`twistOne hM`; `twistOneModuleIso hM U` identifies its chart pullback with the
relative degree-one module sheaf on `P^n_U`.

For every inclusion `hUV : U ≤ V` of frame opens,
`twistOneModuleIso_restrict` proves the equation

```text
(chartMap hUV)^*(twistOneModuleIso V).hom ; (chartTwistIso hUV).hom
  = compHom(chartMap hUV, chart V, chart U) ; (twistOneModuleIso U).hom.
```

Here `;` denotes composition from left to right. The source is the pullback
along `chartMap hUV` of the pullback along `chart V` of the global degree-one
module. The target is the relative degree-one module on `P^n_U`. The comparison
`compHom` uses the proved equation `chartMap_chart`; the transition
`chartTwistIso` includes the full dual-frame change and projective base change.
The restriction compatibility is a conclusion.

The definition `twistOneRestrictionIso hM hUV` constructs the actual isomorphism
with this source and target. It pulls `twistOneModuleIso hM V` back along
`chartMap hM hUV` and composes with `chartTwistIso hM hUV`.
The theorem `twistOneRestrictionIso_hom` identifies its hom with the canonical
composition comparison followed by `twistOneModuleIso hM U`, by the restriction
equation above. Thus this construction agrees with direct comparison on the
smaller chart, including the canonical pullback associativity map.

The proof first establishes two generic normalization facts.
`RefinedPullbackComparison.normalize_id_left` says that refinement along the
identity adds exactly the inverse canonical identity-pullback comparison.
`normalize_identity` then shows that an identity chart comparison normalizes to
the identity on the actual identity pullback. Their proofs use pullback-unit
naturality, the identity-left composition law, and inverse cancellation.

The generic lemma `restriction_of_normalized_overlap` works with schemes
`X,U,V,O`, maps `a : U → X`, `b : V → X`, `c : U → V` with `c ; b = a`, and
maps `f : O → U`, `g : O → V` with `f ; a = g ; b`. It assumes a map
`t : U → O` satisfying `t ; f = id` and `t ; g = c`. Given a module `G` on `X`,
isomorphisms `ea : a^*G ≅ M`, `eb : b^*G ≅ N`, `e : c^*N ≅ M`, and an
overlap isomorphism `φ : f^*M ≅ g^*N`, it assumes the actual descent equation
for `ea,eb,φ` and a normalization equation for `t^*φ` followed by `e`.
It concludes `c^*(eb.hom) ; e.hom = compHom(c,b,a) ; ea.hom`.
No openness or Cartesian property is needed for this generic lemma.

To prove it, the descent equation identifies `φ` with the canonical
`CommonSourceCocycle.transition`. The published `transport_transition` law
transports this transition along `t`. The normalization hypothesis simplifies
the result to the canonical identity-pullback comparison. Finally
`square_normalize`, pullback-unit naturality, and cancellation yield the
restriction equation.

For the concrete frame charts, `chartMap_id` specializes the existing reflexive
chart-map identity. `twistNormalize_id` applies the generic identity-normalization
lemma to the already proved identity law for `chartTwistIso`.
`overlapTwistIso_restrict_normalize` takes
`O = P^n_U ×_(frameBundle) P^n_V` and the actual map
`t = pullback.lift id (chartMap hUV)`. It specializes
`overlapTwistIso_normalize` to the smaller chart `U`, cancels the canonical
identity-pullback comparison, and obtains the required normalization equation.
The final theorem applies `restriction_of_normalized_overlap` to this equation
and the published `twistOneModuleIso_compatible` descent law.

The result supplies a restriction law for the existing global degree-one
bundle. It does not construct a global evaluation pullback isomorphism,
frame-choice comparison, cubic embedding, or moduli scheme. The host
`LargeLevelRepresentabilityStatement` remains a separate proof obligation.
