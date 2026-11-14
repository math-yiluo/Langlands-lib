# Generic Chevalley closures over Dedekind domains

This internal construction applies the Library schematic-closure construction
to an actual field Chevalley group `C : D.ChevGroup K`, embedded by `C.i` into
the standard general linear group. The base `R` is a Dedekind domain with
specified fraction field `K`.

`ambientModel D R K` is the standard matrix group over `R`, with the Library
base-change isomorphism as its specified generic identification. Its flatness
and finite type follow from the published smoothness of the general linear
group.

`genericModel D R K C` is the schematic closure of `C` in that matrix model.
It is an actual affine flat finite-type group scheme. `genericModelHom` is
the compatible model homomorphism, and `genericModelHom_isSchematicClosure`
records that its closed embedding has exactly the kernel ideal sheaf of the
original generic morphism. `modelInclusion` is that embedding into matrices.
`modelInclusion_generic` is its compatibility square with the specified
generic identification. Since Dedekind domains are Noetherian, this model is
also locally of finite presentation.

`liftedIntegers_domain` and `liftedIntegers_principal` transport the domain and
principal ideal properties of the integers through the ring equivalence
with their universe lift.
`integerGenericGroup D` chooses one field Chevalley group over the fraction
field of `ULift ℤ`, and `integerModel D` closes that single group in the
matrix group over `ULift ℤ`. This choice precedes any later field fibres.

The provenance is internal: these are specializations of the existing
matrix group, field Chevalley group and Dedekind schematic-closure
constructions. No special-fibre comparison, smoothness or reductivity of the
closure is asserted here.
