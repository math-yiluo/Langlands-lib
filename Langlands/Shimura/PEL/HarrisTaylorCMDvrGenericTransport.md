# Transporting the generic polarized action to the generic fibre of a good model

An abelian-scheme isomorphism from a specified generic fibre to the
underlying abelian scheme of a polarized rational action transports the
whole polarized action. The constructor `transportDvrGenericPolarizedAction`
uses conjugation in the rational category for the action. The given
dual witnesses specify the target of the polarization, which is the
integral pullback by the isomorphism and its dual. Both maps are isogenies,
so the Library's pullback theorem supplies the relative polarization.

Conjugation preserves addition and rational scalars by bilinearity of
composition. It preserves faithfulness and its intertwining equation
gives `transportDvrGenericActionIso`. Naturality of dual pullback along
this intertwiner transports the actual involution equation. The integral
polarization also satisfies the rational dual-pullback equation after
rationalization. The construction applies the Library's rational action and
integral dual-pullback results to the generic identification of a good model.
