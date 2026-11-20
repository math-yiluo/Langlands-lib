# Schematic images of residue-fibre sections

Let `q : T ⟶ S` have affine Noetherian source, and let `p : X ⟶ T`
be separated, quasi-compact and locally of finite type, with `X` locally
Noetherian. A `ResidueFibreSections` family consists of a preimmersion
`q.fiber s ⟶ X` for each `s : S` whose composite with `p` is the fibre inclusion.
`DvrExtension` asks that every map from the spectrum of a discrete valuation
ring to `T` lift to `X` with range contained in the union of these preimmersions.
Under this condition, `finiteImage_of_dvrExtension` proves that the schematic
image of any map from a Noetherian scheme with range in this union is finite
over `T`.

Over a field, a map with image in one of the preimmersions factors through it.
Its pullback along the field point is a surjective preimmersion into a reduced
scheme, hence an isomorphism. The fibre inclusions are monomorphisms, so two
field points in the family that have the same projection to `T` agree.

The union of images is stable under specialization. A nontrivial
specialization in `X` comes from a discrete valuation ring. The lifting
hypothesis and the field-point comparison give two maps on this valuation
test that agree at the generic point. Schematic dominance of the generic
point and separatedness of `p` identify the maps. The closure of the image of
a Noetherian source stays in the union, since it is the union of the closures
of the images of the finitely many generic points of irreducible components.

The schematic image therefore projects injectively to `T`, giving local
quasi-finiteness. For the discrete valuative criterion, the lift supplied by
the family agrees with the given point of the schematic image over the fraction
field. Schematic dominance implies that the defining ideal of the schematic
image also vanishes on the valuation test. The valuative criterion gives
universal closedness. Along with separatedness and finite type, this gives
properness, and a proper locally quasi-finite morphism is finite.

This internal argument supplies the finite schematic image used to glue the
graphs of the residue-field maps in the adic Hom proof. It uses the Library's
Noetherian DVR specialization and discrete valuative criterion.
