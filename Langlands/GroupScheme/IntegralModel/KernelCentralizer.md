# Integral models of full character-kernel centralizer components

Lean module: `Langlands.GroupScheme.IntegralModel.KernelCentralizer`.

Worker 209, with Worker 200, for the kernel-centralizer construction in
Task 6404. This is derived infrastructure assembled from published Library
results. All constructions preserve an arbitrary universe `u`.

## Source and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
introduce the integral group `M_a` immediately before Theorem 8.2.9
(printed p. 293 / PDF p. 324). It is the relative identity component
of the centralizer of the full character kernel `C_a` in the smooth
ambient model. The source states that it is smooth and affine and that
its generic fibre is the identity component of the generic centralizer.
The ensuing proof uses this group in its rank-one argument
(printed pp. 294–295 / PDF pp. 325–326).

The present construction supplies this model and its actual ambient
inclusion for a smooth integral model and any map from a split integral
torus. Generic connected reductivity follows when the ambient generic
group is connected reductive and the generic character is nonzero.
Root-group comparisons, residue radicals, Weyl lifts and the final
opposite-factor criterion are subsequent proof obligations.

## Full centralizers

`RelativeRoot.kernelCentralizer_hasSmoothClosedRepresentative_overRing`
works over any commutative integral domain `R`. Its parameters are an
affine smooth group `G`, a split torus `T`, a map `i : T → G`, and an
arbitrary character `a` of `T`.

The proof uses `Diagonalizable.kernelDiagonalizableIso` to identify the
actual character kernel with the diagonalizable group for the quotient
lattice `X*(T)/ℤa`. It applies the published smooth closed
diagonalizable-centralizer construction to the composite of the inverse
isomorphism, the actual kernel inclusion and `i`. Invariance of the
all-test range under a source isomorphism identifies the resulting
centralizer with `RelativeRoot.kernelCentralizer i a`. Thus the output
represents the full centralizer on every test scheme. The lattice
quotient retains torsion. The character may be zero or nonprimitive,
and the kernel may be nonreduced.

## Identity components and the generic fibre

Over a field `k`, let `G` be smooth and affine and let `i : H → G`
represent its relative identity component, with `H` geometrically
connected. `IsRelativeIdentityComponent.identityComponentIso` constructs
an isomorphism `H ≅ identityComponent G`. Its forward map is the
ordinary identity-component factor of `i`. Its inverse lifts the
ordinary identity-component inclusion through `i`, using the published
lifting theorem for homomorphisms from geometrically connected groups.
The two inverse identities follow by cancellation of the corresponding
monomorphisms. `identityComponentIso_hom_comp` identifies the forward
map followed by the ordinary component inclusion with `i` itself.

Now let `R` be a domain with fraction field `K`, let `M` be a smooth
integral model, and let `i : H → M.group` represent its relative
identity component, with `H` geometrically connected.
`IntegralModel.componentGenericIso` applies the published arbitrary-base
compatibility of smooth relative identity components and then the
preceding field isomorphism. Its target is the ordinary identity
component of `M.genericFibre`, the actual pullback before the model's
chosen generic identification. The theorem
`componentGenericIso_hom_comp` gives compatibility with the actual
base change of `i`.

When `R` is a discrete valuation ring and `H` is smooth,
`IntegralModel.componentModel` is the integral model with group `H`
and this generic isomorphism. Affineness follows from the published
smooth DVR affineness theorem for relative identity components.
Smoothness supplies flatness and local finite type.
`componentInclusion` is the compatible model map into `M`; its
specified generic map is the ordinary identity-component inclusion
followed by `M.genericIso.hom`. The generic group of `M` may be
disconnected.

## The chosen centralizer data

`IntegralModel.KernelCentralizerData M i a` records an actual smooth
affine full centralizer `C`, its closed inclusion into `M.group`,
its all-test representation property, and an actual smooth relative
identity component `H → C` with geometrically connected fibres.
`nonempty_of_split` constructs these data when `M` is smooth and the
integral torus is split: first use the full-centralizer theorem,
then `RelativeIdentityComponent.smoothExistence`. Affineness of `C`
follows from its closed inclusion into the affine ambient model.
`ofSplit` chooses one such datum.

For any datum `D`, `D.fullModel` regards `C` as a model of its actual
generic fibre, using the identity isomorphism. `D.fullInclusion`
maps it into `M`; `fullInclusion_isClosed` records closedness.
`D.fullGenericRepresents` applies the published full-kernel
base-change theorem to identify this generic full centralizer with
the kernel centralizer of the actual base-changed character and
torus map.

Over a DVR, `D.model` applies `componentModel` to `H → C`. Its group
is `H`, with smoothness and geometric connectedness recorded by
`model_isSmooth` and `model_geometricallyConnected`. `D.inclusion`
has integral map `H → C → M.group`. Its generic map is the
ordinary component inclusion, followed by the base change of the
full centralizer inclusion and then `M.genericIso.hom`. Its
compatibility square follows from functoriality of base change
and `componentGenericIso_hom_comp`.

Finally, `D.generic_isConnectedReductive` needs only the domain
and fraction-field assumptions. If the specified generic ambient
group is connected reductive, the integral torus is split and
the actual generic character is nonzero, it proves connected
reductivity of `identityComponent D.fullModel.genericFibre`.
It transports ambient reductivity through `M.genericIso`, base
changes closedness and splitness, and applies the published
`RelativeRoot.kernelCentralizerComponentReductive` to
`D.fullGenericRepresents`. This uses the full character kernel
throughout.
