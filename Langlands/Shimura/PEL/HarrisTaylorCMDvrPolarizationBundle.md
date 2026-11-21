# The ample diagonal bundle of an extended dual-valued homomorphism

For a good abelian model over a DVR and specified dual witnesses,
`extendDvrDualHom` extends a homomorphism from the actual generic fibre
to its dual. It first uses the inverse of the canonical comparison of
actual duals to identify the map as a homomorphism between generic fibres.
The integral generic Hom bijection then gives the unique homomorphism on
the given model. `pullbackMap_extendDvrDualHom` identifies its pullback
with the original map under that dual comparison.

For a generic polarization, `extendDvrAmpleDiagonalBundle` forms the
actual diagonal Poincaré bundle from this extension and proves it ample.
Over an algebraic closure of the fraction field, the field-ample Mumford
presentation makes the diagonal bundle ample. The existing diagonal
base-change isomorphism identifies the bundles and field-base-change
reflection gives ampleness on the fraction field. The ample-fibre locus
of the diagonal bundle over the DVR is closed and contains the generic
point. Its residue-field restrictions are therefore ample at all points.
Proper fibrewise ampleness over an affine noetherian base gives ampleness
of the actual bundle on the good model.

This is a derived application of the Library's DVR Hom bijection, canonical
dual comparison, diagonal Poincaré geometry and fibrewise ampleness. The
identification of a relative polarization from the total ample bundle is a
further step in the extension argument.
