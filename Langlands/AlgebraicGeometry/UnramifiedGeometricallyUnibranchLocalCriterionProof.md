# Local algebra for the geometrically unibranch etale criterion

Authors: Worker 384 and Worker 706.

The theorem
`Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionProof.unramifiedGeometricallyUnibranchLocalCriterion`
proves exactly the published
`UnramifiedGeometricallyUnibranchLocalCriterionStatement.{u,v,w}`.
The base domain `R`, source domain `S`, and arbitrary model `Rp` of the
base localization retain independent universes. All hypotheses and the
principal-neighborhood etale conclusion are unchanged.

The imported internal module `GeometricallyUnibranchEtaleDomain` supplies
the local-domain consequence of geometric unibranchness. Its theorem
`isDomain_atPrime_of_geometricallyUnibranch` shows that an etale algebra
localized at a prime is a domain when the contracted base localization
satisfies the actual normalization and purely inseparable residue-field
predicate. It treats arbitrary localization models directly. The proof
normalizes the local base, proves the relevant tensor product local using
integrality and the purely inseparable residue extension, applies the
published normal-base etale domain-localization theorem, and descends the
domain property along the injection given by flatness. Its paired Markdown
explains these steps and the localization-model adapter.

The assembly theorem `localCriterion_of_etale_domain_localizations`
packages the remaining argument with that local-domain consequence as an
explicit premise. The final theorem supplies the proved bridge, so the
exact result has no additional premise. The argument below does not impose
birationality, a trivial generic extension, Noetherianity, flatness of `S`,
or finite presentation of `S`.

Flatness and going down show that each minimal prime of an algebra over a
domain lies over zero. Quasi-finiteness makes this set finite. An etale
algebra over a domain embeds in its generic fiber by flatness; the formally
unramified generic fiber is reduced.

For a reduced ring with finitely many minimal primes, choose one element
outside the specified prime in each minimal prime not contained in it.
Their product is outside the specified prime and annihilates the kernel of
the prime localization. Indeed a product with a kernel element belongs to
every minimal prime and hence is zero by reducedness. This proves that the
principal localization embeds in a localization of the local domain.

The assembly proof first takes Mathlib's standard etale
presentation surjecting onto a principal localization of `S`. It pulls
back the chosen prime and applies the bridge and the preceding
neighborhood lemma to obtain a domain principal localization of the
presentation algebra. Localizing the surjection gives a map of domains.
Both its prime kernel and the zero ideal contract to zero in `R`, since
the map from `R` to the target is injective. Quasi-finite incomparability
therefore makes the kernel zero. The resulting algebra isomorphism
transports etaleness to the localized target.

Finally, the numerator of the image of the chosen presentation element
gives the requested principal neighborhood of `S`. Its image is associated
to that presentation element after the first localization. Mathlib's
localization composition and associated-element lemmas identify the
iterated localization with localization at the product of the first
element and this numerator. Both factors avoid the specified prime.

The construction is an internal algebraic reduction of the proof route in
Stacks Project tag [0GSC](https://stacks.math.columbia.edu/tag/0GSC), retained
as source `stacks-dominant-unramified-etale-2026-11-01`. It uses no
Noetherian hypothesis and replaces the source's generic norm argument by
quasi-finite incomparability. The etale local-domain consequence of geometric unibranchness used in
that source is proved in the imported internal bridge module. The exact
published statement and its imported dependency closure are unchanged.
