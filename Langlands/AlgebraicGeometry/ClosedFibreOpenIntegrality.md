# Geometric integrality of opens meeting the closed fibre

This internal module supplies the fibre conditions needed for the affine
opens in the valuation-ring extension construction. Its base is any local
commutative ring in an arbitrary universe. It does not require a
Noetherian, domain, or valuation-ring assumption.

`geometricallyIntegral_open_of_surjective` states that the restriction of
a geometrically integral morphism to a source open remains geometrically
integral if that restriction maps onto the base. For each field-valued
base change, the proof identifies the restricted pullback with an open
subscheme of the original integral pullback, using the pullback-pasting
isomorphism. Base-changed surjectivity gives nonemptiness. A nonempty open
subscheme of an integral scheme is integral, as required.

`geometricallyIntegral_of_smooth_geometricallyConnected` derives geometric
integrality of a smooth geometrically connected morphism over any base
from the Library's theorem over fields. It applies that theorem to every
residue-field fibre and then uses Mathlib's fibrewise criterion.

`surjective_open_of_meets_closedFibre` proves that an open meeting the
closed fibre of a universally open morphism to a local spectrum maps onto
the base. Its image is open and contains the closed point. Every point of
the local spectrum specializes to the closed point, so every point belongs
to that image.

`geometricallyIntegral_open_of_meets_closedFibre` combines these facts:
every total open meeting the closed fibre of a smooth geometrically
connected morphism to a local spectrum has geometrically integral fibres,
including nonempty fibres. This conclusion applies to affine opens but
does not assume affineness. No projectivity or line-bundle extension is
claimed.

The provenance is internal: the proof combines Mathlib's geometric
integrality, base-change, open-immersion and specialization results with
the imported Library smooth geometric integrality proof.
