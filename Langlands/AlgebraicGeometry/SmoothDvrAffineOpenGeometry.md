# Smooth DVR affine-open geometry

This internal helper develops the geometric inputs for affineness of the
relative identity component. It reuses `exists_irreducible_open` from
`ConnectedLocallyNoetherianDomainStalksIntegralProof.lean`, exposed there
during integration without changing its statement or proof. Finite
generation of the kernel of prime localization makes a nearby principal
localization a domain, and affine neighborhoods transfer this to schemes.
The neighborhood statement requires no connectedness premise.

A DVR spectrum consists of its zero ideal and its maximal ideal. An internally
chosen irreducible element generates the maximal ideal, so its principal
open is precisely the generic singleton. These claims use Mathlib's DVR
and prime-spectrum definitions.

`isAffineOpen_of_fiberwise_closed` proves that an open subset `U` of a smooth
affine scheme `X` over an arbitrary DVR is affine if its intersection with each
topological fibre is closed in that fibre. Smoothness supplies local finite
type, hence local Noetherianity, and regular local stalks through the published
`Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing`. The published
`IsRegularLocalRing.isDomain` then supplies domain stalks and the local
irreducibility lemma applies. Choose an irreducible element of the DVR
internally. Its principal open in the base is the generic singleton, dense
because the DVR is a domain. Smoothness implies that the structural morphism
is open, so the preimage of this singleton is dense. It is the principal open
of the pulled-back global section.

Fibrewise closedness gives closedness on this generic principal open by the
homeomorphism induced by equality of the two subsets. The closed point is the
complement of the generic singleton. Its fibre is closed in `X`, so its closed
subset `U` intersected with that fibre is closed in `X`. The principal-open
criterion in `FibrewiseClopenAffineOpen.lean` now proves affineness. The argument
uses no group structure and makes no henselian or residue-field assumption.

This is a derived proof route for the affineness part of Prasad–Yu §3.5; it
does not assert that their Proposition 3.1 has been formalized. The uniformizer
is chosen inside the proof and is absent from the theorem's premises.
