# Coordinate root data on an arbitrary base scheme

This internal infrastructure extends actual coordinate root data to an
arbitrary scheme base. `CoordinateRootDatum.IsRealizedOver` uses the actual
group fibre at each supplied field-valued point, with the canonical split
torus coordinate identification. `IsGlobalCoordinateRootDatumOf` requires
a finite reduced datum realized on every such field fibre.

`exists_identityEquiv_of_actualField` compares two full data realized on
the same split maximal torus of a connected reductive group over a field.
The published root-datum uniqueness theorem identifies their roots and
coroots; the coordinate pairings both equal the integral dot product.
Together these give a full equivalence fixing both coordinate lattices.

`isRealizedOver_baseChange_iff` uses the canonical composition isomorphism
for group pullbacks and the compatible split-torus identifications. Actual
root data transport along ambient group isomorphisms.

`exists_open_schemeCoordinateRootDatum` restricts to an affine chart
through a prescribed point and applies the published full affine
root-datum neighbourhood theorem. A field-valued point in the chart image
factors uniquely through the open chart. Expressing this factorization
as its actual ring map invokes the affine theorem with the original field
algebra structure, and the pullback comparison returns the conclusion
to the actual fibre of the original group over the original scheme.

`schemeCoordinateRootDatumAtPoint` is the concrete chosen-data construction supplied by these
existence lemmas. It uses classical choice on the proved existence result;
the preceding lemmas state and prove its mathematical existence and scope.
