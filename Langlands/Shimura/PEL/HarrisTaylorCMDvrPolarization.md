# Extending a generic polarization after doubling over a DVR

The input is a good abelian model with its dual witnesses and a
polarization on the actual generic fibre. `extendDvrPolarizationDouble`
uses the ample diagonal Poincaré bundle of the extended dual-valued
homomorphism to give a polarization over the DVR. Its homomorphism is
twice the integral extension from `extendDvrDualHom`.
`pullbackMap_extendDvrPolarizationDouble` identifies its restriction to
the generic fibre with twice the given polarization.

The normalized Mumford family commutes with the canonical comparison of
duals and the actual base change of a line bundle. Over the fraction
field its classifier depends only on the isomorphism class of the
underlying line bundle, by the formula for the forgotten Mumford class
and injectivity of the point-class map. The Mumford map of the diagonal
Poincaré pullback on the generic fibre is twice its polarization. The
same equation holds on the good model by injectivity of generic
restriction from a flat source to a separated target.

The actual total diagonal bundle is ample. Its Mumford presentation
pulls back to every geometric fibre, and yields an isogeny over each
algebraic closure of a residue field. Faithfully flat field descent
then gives the isogeny over each residue field, and the fibrewise
isogeny criterion applies to the total homomorphism. Together the
fibre presentations and this total isogeny give the relative
polarization predicate.

The proof combines the published diagonal Mumford formula, canonical
dual comparisons, generic Hom injectivity and the Library's isogeny
criteria. The factor of two comes from the diagonal bundle formula.
