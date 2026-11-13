# Connected fibres under unramified model descent

This is an internal consequence of scheme fibre base change, surjectivity of the
integer-spectrum map for an extension of valued fields, and the published actual
integral-model interfaces. It supplies the connected-special-fibre step in the
Iwahori-model assembly; it asserts no existence or descent of an integral model.

For any group scheme over any base and any surjective base change, connectedness
of every actual residue fibre of the base change implies connectedness of every
original residue fibre. A point of the original base lifts through the surjective
map. The comparison of residue fibres is a pullback along a map of spectra of
fields. That map is surjective, so the fibre comparison is surjective. The
original fibre is therefore a continuous surjective image of a connected space.
An isomorphism of group schemes over the same base also transports the all-fibres
condition, by pulling the isomorphism back to each residue fibre.

For an actual integral model over a local domain, the construction
`specialFibreHomeomorphClosedFibre` identifies the topology of its full special
fibre over the local residue field with the topology of its canonical scheme
fibre at the closed point of the base spectrum. Both project by embeddings onto
the same inverse image of that closed point. This proves that connected fibres
imply a connected full special fibre.

For a nonarchimedean local field, the actual integer-spectrum map to the integers
of its maximal unramified extension is surjective by `valuationInteger_fpqc`.
Thus connected fibres of `M.baseChangeUnramified` descend to `M`. More generally,
if a supplied model `N` is isomorphic to that base change and has connected
fibres, `hasConnectedSpecialFibre_of_unramified_iso` proves that `M` has connected
special fibre. It first transports connected fibres across the supplied actual
model isomorphism, then reflects the fibre condition and applies the closed-point
homeomorphism. These are ordinary connected fibres, and no geometric-connectedness
hypothesis is needed. All assertions hold in arbitrary universe `u`.
