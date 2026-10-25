# Cuspidal constituent maps with independent carriers

This internal construction applies the published
`CuspidalSupport.leviCuspidalConstituentTheorem` to two representations whose
carrier universes may differ. The independent universes `uF`, `uV`, and `uW`
belong to the field, ambient representation `A`, and constituent `D`.
Every block shape is allowed, including rank zero.

The inputs are actual bundled complex representations of the same product
Levi, admissibility of `A`, irreducibility and Levi cuspidality of `D`, and an
actual occurrence witness: an invariant subspace `S` of `A` and a surjective
intertwiner from `S` onto `D`. Levi cuspidality includes admissibility and
smoothness of `D`. There is no cuspidality, central-character, or finite-length
assumption on `A`.

`leviCuspidalConstituentMaps` chooses two actual intertwiners on the original
carriers: an embedding `D → A` with an injectivity certificate, and a quotient
`A → D` with a surjectivity certificate. These maps are chosen independently;
the construction neither asserts a splitting nor specifies their composite.
It is noncomputable because it selects witnesses of the published existence
theorem.

The helper theorem `leviCuspidalConstituent_maps` establishes the existence of
these maps. Its proof bundles the smooth actions and lifts both carriers to
the common universe `max uV uW` using `Category.UniverseLift`. It also lifts the
given invariant subspace. Composing its inclusion and quotient with the
canonical up/down equivalences gives actual injective and surjective
intertwiners in that common universe. The published
`SmoothRep.isSubquotient_iff_exists` converts them into the subquotient relation
used by the constituent theorem. Admissibility, irreducibility and cuspidality
transfer along the carrier equivalences. Applying the published theorem there,
and conjugating both resulting maps by up/down, returns maps on the original
carriers.

The provenance is internal: this is a carrier and occurrence-interface adapter
for an already published theorem, not a new literature assertion. Its
mathematical input is `ConstituentProof`; its transport inputs are
`Category.UniverseLift`, `LeviDefinitions`, and
`Classification.SupercuspidalSupport`. It supplies an input to the relative
Jacquet comparison but does not prove any Jacquet multiplicity comparison,
opposite adjunction, or head theorem.
