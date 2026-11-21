# Square-integrability at the CM-conjugate finite place

`Langlands.Global.Harris.HarrisSquareIntegrableConjPlaceStatement` concerns an
actual cuspidal realization `S` of `GL_(r+1)` over a CM number field `E`, under
the Library's compactness hypothesis on `AdeleQuotient E`. Fix its spectral
presentation `P`, with irreducible admissible components at **every** finite
place, and a finite place `v`. If the global class is conjugate self-dual and
the presented component at `v` is square-integrable, the component of the
same presentation at `conjPlace E v` is square-integrable. Here
`IsSquareIntegrable` includes irreducibility and uses square-integrability
modulo the center for the canonical local topology of the completion.

The all-place condition allows `CuspidalSpectralPresentation.finiteSliceEquiv`
to identify the supplied slice with the actual irreducible finite factor.
It is not automatic for a spectral presentation: a finite-invariant slice
can have multiplicity absorbed into a factor at an exceptional place.

## Provenance and boundary

This derived input relates Harris, *The local Langlands conjecture for GL(n)
over a p-adic field, n < p* (1998), §1, Theorem 1.2(i)–(ii), p. 185, to
Clozel, *Représentations galoisiennes associées aux représentations automorphes
autoduales de GL(n)* (1991), §5.3, Theorem 5.7, p. 142. Harris assumes a
square-integrable constituent at one place; Clozel uses the components at
both members of a split pair. The proof obligation is to identify the
conjugate-place constituent with the smooth contragredient of the original
constituent after transport by the CM-induced completion isomorphism, and
then transport square-integrability through both operations.

Only the proposition is defined here. Distinctness and exhaustion of the
places above the real subfield place are separate arithmetic inputs; neither
is needed for this implication. No supercuspidality or ramified Galois
comparison is asserted.
