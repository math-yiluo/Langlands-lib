# Internal direct sum of central Hecke ideals

This derived unit supplies the additive direct sum argument used in Renard
(9 July 2026), VI.7.4, printed pp.185–186 / PDF pp.191–192. It imports the
categorical central multiplier and central ideal constructions.

`centralMultiplier_finite_sum` transfers finite vectorwise reconstruction by
central operators to the Haar Hecke algebra through its linear equivalence
with the lifted regular carrier. For an orthogonal idempotent family with that
reconstruction, `centralIdeals_isInternal` proves that the canonical additive
map from the external direct sum of the fixed ideals to the Hecke algebra is
bijective. Applying each multiplier recovers the corresponding coordinate,
proving injectivity. The finite support of the multipliers of a given Hecke
element supplies a preimage, proving surjectivity.

`centralIdealsAddEquiv` bundles this proved bijection as an actual additive
equivalence from the external direct sum to the Hecke algebra. Its forward map
is exactly the canonical sum of the ideal inclusions, as recorded by
`centralIdealsAddEquiv_apply`.

`decomposition_centralIdeals_isInternal` applies this result to the canonical
projectors supplied by an actual smooth category decomposition. The index
universe is independent of both the group and carrier universes; no finiteness
assumption on the set of indices is used. The actual Bernstein decomposition
and the equivalences of its blocks with ideal modules remain separate
obligations.
