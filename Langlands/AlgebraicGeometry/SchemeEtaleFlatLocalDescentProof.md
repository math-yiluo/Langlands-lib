# Pointwise etale descent in a flat scheme pullback

This private draft constructs the affine-section and stalk bridge for
descent of the etale locus. Its affine helper starts from the actual
section-ring pushout, localizes one original source ring and the
pullback section ring at their stalk primes, and uses the published
prime-localization criterion to identify the pullback stalk as a
localization of the partially localized tensor product. The local
algebra differential descent lemma then applies.

For schemes, choose affine neighbourhoods of the two image points and
their common image. Their pullback is affine. Its section square is a
pushout and its actual germs give the compatible localizations required
above. Flatness of the projection to the original source gives faithful
flatness of its local stalk map. Formal unramifiedness over the other
stalk composes with its affine-chart localization. The affine helper
gives formal unramifiedness over the base section ring, which restricts
to the base stalk. These are internal consequences of the published
affine pushout, localization, and flatness APIs.

For flatness, compose the flat stalk map of the other base morphism
with the assumed flat pullback stalk map. The commutative square and
the formula for stalk maps of composites identify the result with the
composite through the original source stalk. The faithfully flat
reflection lemma then proves flatness of that source stalk over the base.

`stalkEssFinitePresentation` supplies essential finite presentation of
the original local-ring map. The local algebra criterion for a flat,
formally unramified local map essentially of finite presentation gives
formal etaleness. The theorem `schemeEtaleFlatLocalDescent` proves
exactly `SchemeEtaleFlatLocalDescentStatement`, deriving flatness of
the projection `a` from the cartesian square and flatness of `g`.
