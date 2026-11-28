# Geometric point transport of normalized CM witnesses

`PolarizedWeilLevel.pointMapData_witness` moves a witness along an
isomorphism of geometric fibre functors. The represented objects,
rational isomorphism and multiplier are fixed. Naturality of the pointed
level equivalence in the fibre-functor isomorphism moves the two orbits
and preserves the witness equation.

`levelDataBaseChange_pointMapData` compares this point transport with
pullback of Harris representatives, using the induced path over the
original base. `levelDataBaseChange_pointMapData_snd` gives the orbit
comparison for separately chosen paths to the image points, using the
monodromy invariance of the orbits. In
`levelDataBaseChange_witness_move`, the object comparison
`levelDataBaseChange_fst_eq` and these orbit transports let one move a
witness between two points of a pulled-back pair.

`levelDataBaseChange_comp_witness` equips the canonical
direct-to-successive pullback isomorphism with multiplier one and the
corresponding orbit equation. It uses the polarization and level
composition comparisons for `levelDataBaseChange`.
`levelDataPointEq_pointMapData` compares transport along an equality of
geometric point maps with paths from a common point. It reduces the
equality of maps by substitution and uses independence of the chosen
path for the invariant orbit.
