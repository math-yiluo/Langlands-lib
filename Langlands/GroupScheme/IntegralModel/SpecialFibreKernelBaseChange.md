# Special-fibre kernels under local coefficient extension

This is an internal derived comparison for actual integral models. Let `R` and
`A` be local domains with fraction fields `K` and `L`. The algebra maps form the
coefficient square required by `IntegralModel.baseChange`, and the map
`R → A` is local. There is no finiteness or unramifiedness requirement on this
extension.

`residueCoefficientSquare` identifies the two maps from `Spec κ(A)` to `Spec R`.
`specialFibreBaseChangeIso` composes the two pullback-composition isomorphisms
with this equality. It compares the extension of `M.specialFibre` from `κ(R)`
to `κ(A)` with the actual special fibre of `M.baseChange A L`.
`Hom.specialFibreBaseChangeIso_naturality` proves the comparison commutes with
every compatible model homomorphism. Its proof uses naturality of the
pullback-composition isomorphisms and transport along an equality of base maps.

`Hom.specialFibreKernelBaseChangeIso` first applies the published
`kernelBaseChangeIso`, then the published `kernelSquareIso` to this naturality
square. Thus it identifies the full scheme-theoretic kernels, including their
scheme structures and group laws. It does not replace the kernel by its identity
component or by its subgroup of rational points.

`Hom.specialFibreKernel_properties_of_baseChange` reflects smoothness,
connectedness and unipotence of the full special-fibre kernel from the model
with extended coefficients. The proof transports the three properties through
the kernel isomorphism. The residue-field extension is fpqc, so the published
`smooth_of_baseChange` and `connectedSpace_of_baseChange` reflect the first two
properties. The kernel is affine because its inclusion into the affine source
is closed, the target being separated. The published
`IsUnipotent.of_baseChange` therefore reflects unipotence.

These declarations are derived from published pullback, kernel and
field-extension reflection results. They make no additional literature claim.
For Task 6317 they supply a comparison needed to descend geometric kernel
properties. The actual geometric kernel hypothesis over the extended
coefficients, parabolicity and the reduction-preimage theorem remain separate
obligations.
