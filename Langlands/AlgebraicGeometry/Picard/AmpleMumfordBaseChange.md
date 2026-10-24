# Ample Mumford presentations under actual dual base change

This auxiliary module makes the equality with an ample line bundle's Mumford
map precise, including the comparison of dual schemes after base change. It is
infrastructure for the field polarization condition, not a definition of a
polarization by itself.

`HasAmpleMumfordPresentation preservation square A hA f` means that there is an
ample line bundle `L` on `A` whose normalized Mumford classifier is `f`. It
quantifies an inverse `B` of `e*L` and its evaluation to `O_S`, then an inverse
`M` of the normalized bundle and its evaluation to `O_A`. The normalized bundle
is `N = L tensor A*B`. The constructed family is
`m*N tensor p1*M tensor p2*M`, with its existing unit rigidification. Ampleness
is required of the original `L`, using the published section-generation-locus
predicate. It is not silently replaced by ampleness of `N`.

These evaluation isomorphisms are explicit witnesses for inverse line bundles;
they are not abstract maps to a prospective dual. The map in the equality is
already constructed by the actual universal rigidified Picard-zero family.
`preservation` is the named canonical pullback-tensor comparison theorem and
`square` is the named Picard-zero theorem for that actual Mumford family. Their
truth is not assumed implicitly or proved in this module.

For fixed line-bundle and evaluation choices,
`eq_mumfordSchemeMapOfLineBundle_iff` proves that equality with this classifier
is equivalent to existence of a rigidified isomorphism between its Poincare
pullback and the normalized Mumford family. The forward implication uses the
existing classifier's pullback isomorphism. The reverse implication applies
its universal-property uniqueness. The isomorphism is required to preserve the
rigidification, and no uniqueness of isomorphism witnesses is claimed.

For any `b : S' → S`, `dualBaseChangeMap` first applies the actual scheme
pullback functor to `f`. It then composes with `dualSchemeBaseChangeIso`, the
unique comparison specified by the pulled-back Poincare family. The resulting
map lands in the chosen dual of `A_{S'}` obtained from
`hasDualScheme_baseChange`. The theorem input
`universality : PicardZeroUniversalBaseChangeStatement` is explicit.
`HasAmpleMumfordAfterBaseChange` applies the preceding ample-presentation
predicate to this map. The base and both total spaces really are changed;
there is no freely chosen target isomorphism.

## Provenance and limits

The motivating equality is condition (b1) in Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, Chapter XI, Corollary (11.5), printed p.160 (PDF164):
after some field extension, the given homomorphism equals the map associated
to an ample line bundle. Definition (11.6) on that page additionally requires
an isogeny. This module generalizes only the auxiliary equality to a specified
map of bases and explicitly supplied actual dual representability. It neither
asserts relative dual existence nor extends the field polarization theorem.

The normalization and Mumford-map constructions are imported, as is the proof
that the base-change comparison is uniquely Poincare-compatible. The new
relation is derived by combining these existing constructions. All schemes
are in the same universe. The module imposes neither a field hypothesis nor an
isogeny condition and does not claim that the changed map is a homomorphism,
that an ample presentation exists, that it is independent of all inverse
choices, or that comparisons cohere under successive base changes. Those
properties are separate from the equality predicate defined here.
