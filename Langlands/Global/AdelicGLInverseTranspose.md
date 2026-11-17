# Inverse transpose and adelic general linear group maps

This shared module places the existing rational-embedding and finite/infinite
component identities beside `AdelicGL`. All statements concern the actual
inverse-transpose automorphism of matrix units over an arbitrary number field.

`Langlands.Automorphic.inverseTranspose_rational` retains its published name
and implicit field and rank arguments from `DualWhittakerCore/DualCuspidal`.
Its entrywise proof is the identical rational-map argument reviewed with
`TransposeAmbient`. The four identities in
`Langlands.Global.RankinSelbergGlobal.Unfolding` retain their published names,
arguments and proofs from `DualWhittakerCore/DualDecay`: inverse transpose
commutes with the finite and infinite projections and their inclusions.
The adele-ring abbreviation in their types is expanded here.

Both original modules import these same declarations. `TransposeAmbient`
reuses them for its linear involution and paired-coordinate formula. This
relocation removes duplicate identities without changing their hypotheses,
conclusions, or the actual adelic maps.

The component extensionality theorem `AdelicGL.ext_infinite_finite` and the
four `infinite_ofInfinite`, `finite_ofInfinite`, `infinite_ofFinite`, and
`finite_ofFinite` identities are also imported by `CuspidalL2/Basics` from
this module. They are moved with their exact published declarations and
proofs, supplying the shared component calculations without importing the
constant-term development.
