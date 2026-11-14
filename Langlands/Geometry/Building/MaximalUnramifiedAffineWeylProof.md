# Affine roots and affine Weyl containment over the maximal unramified field

`Langlands.Geometry.Building.maximalUnramifiedAffineWeyl.{u}` proves exactly
`MaximalUnramifiedAffineWeylStatement.{u}`, with all its original inputs and
at arbitrary universe `u`. For supplied building data `C` over
`inertiaFixedField F`, it proves both that `C.affineRoots` is an affine root
system admitting rank zero and that its affine Weyl group is contained in the
range of the actual normalizer action on `C.apartment`.

This is an internal specialization of the published theorem
`integerValuationAffineWeyl`. Apply that theorem to the field
`inertiaFixedField F`, its explicit valuation
`MaximalUnramified.valuation F`, the original group scheme `H` and the
original supplied data `C`. The abbreviation
`MaximalUnramified.BuildingData F H` is definitionally the required
`IntegerValuationBuildingData` for this field and valuation, so the resulting
affine roots, apartment and normalizer action are the original ones.

The only additional input required by the generic theorem is a unit of
source-positive real order one. The published
`MaximalUnramified.exists_order_eq_one F` supplies it by mapping a chosen
base-field uniformizer unit into the inertia fixed field. The established
order comparison gives integer order one there, and casting gives real
order one.

The proof introduces every input of the target and applies the generic
theorem with these arguments. It adds no hypothesis or local-field instance
on the inertia fixed field and does not assert existence of building data.
The imported theorem already includes corrected AR4 and rank zero.
Its paired Markdown and that of the unchanged target record the KP
correspondence; this specialization requires no further literature result.
No downstream chamber, integral-twist or cocycle-vanishing proof is used.
