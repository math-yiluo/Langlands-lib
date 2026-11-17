# A torus fibre spreads to an open neighbourhood

Workers 606 and 125.

`Langlands.GroupScheme.torusFibreSpreading.{u}` proves the unchanged
`Langlands.GroupScheme.TorusFibreSpreadingStatement.{u}` for every universe.
The fppf affine structure morphism, the connected residue fibres, and the torus
fibre at the selected point are exactly the hypotheses of the published target.

The proof first makes the structure morphism geometrically connected from its
connected finite-type group fibres. Smoothness of the selected torus fibre then
spreads to an open neighbourhood using `exists_smooth_nhd_of_smooth_residueFiber`.
The actual residue fibre on that open is the scalar extension of the original
fibre along the induced residue-field map. Actual base-change composition
isomorphisms transport the field-torus property across this identification.
The smooth-case theorem supplies an étale splitting map over the open. Its
composite with the open immersion into the original base is still étale and
its image contains the selected point. The relative-torus property descends
to this open image.

The two helpers implement the smooth-locus and split-torus lifting routes of
Conrad, *Reductive group schemes* (2014), Corollary 3.1.8, pp.84–85. The smooth
case uses the published smooth-monomorphism local-isomorphism theorem in place
of the dimension argument. No additional assumptions on the base or fibres
are imposed. All pullbacks refer to the actual group-scheme base-change functor.
