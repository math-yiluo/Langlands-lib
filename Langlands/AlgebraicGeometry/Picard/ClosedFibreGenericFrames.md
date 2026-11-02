# Affine total neighbourhoods carrying generic frames

This is an internal construction for the valuation-ring extension proof.
It combines the total-neighbourhood theorem for smooth valuation schemes with
the closed-fibre coverage theorem. It constructs actual frame sections; it
does not assume or prove that their transition units extend.

For a map `q : Y ⟶ X`, a line bundle `D` on `Y`, and a total point `x`,
`exists_affine_generic_frame` refines a supplied total trivializing
neighbourhood to an affine open containing `x`. The restriction/pullback
comparison converts its trivialization to the input of the published
`Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit`. The resulting section
is restricted to the inverse image of the smaller affine open; the frame
property is preserved by restriction.

For a morphism `p : X ⟶ Spec R` over a commutative local ring,
`ClosedFibreGenericFrames q D p` records an affine total neighbourhood of the
image of each point of the actual scheme-theoretic closed fibre, and an
actual section of `D.obj` over that neighbourhood's inverse image under `q`,
with its `IsFrameOn` proof. Classical choice gives these data from pointwise
total trivializing neighbourhoods.

When `p` is universally closed, the opens cover the entire total scheme.
The method `openCover` returns the actual scheme open cover indexed by the
closed-fibre points. When `p` is smooth and geometrically connected, each open
contains the same chosen generic point of the closed fibre. This follows
because each open contains its indexed closed-fibre point and the closed
fibre is integral.

`smoothClosedFibreGenericFrames` applies this construction to the actual
generic pullback along any supplied fraction field of an arbitrary valuation
domain. The theorem already providing total trivializing neighbourhoods
supplies the existence input.

The final declarations specialize to an abelian scheme's self-product.
The base-change self-product isomorphism identifies its canonical product
map with the projection of the actual generic pullback. Transporting
neighbourhoods along this isomorphism gives
`mumfordProductClosedFibreGenericFrames`, whose sections belong to the
original `D.obj` over inverse images under exactly the target's canonical
`q`. The total opens cover the product by properness and contain its common
closed-fibre generic point by smoothness and geometric connectedness.
The latter uses geometric connectedness of the two smooth projection
factors and its composition theorem.

No rank restriction, Noetherian assumption, chosen replacement fraction
field, or hypothesis about the two unit axes is used. The generic transition
functions still require compatible normalization and total unit lifts.
This construction alone does not extend a line bundle.
