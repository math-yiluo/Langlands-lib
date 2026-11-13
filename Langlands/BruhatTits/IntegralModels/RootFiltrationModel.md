# Supplied smooth connected models of one root-filtration subgroup

This internal data interface records the single-depth root-model input needed
in the neutral-point argument for unramified parahoric models. It introduces no
existence statement. Its ingredients are the published all-test relative root
functor, actual integral models and their compatible generic maps, and the
filtration of supplied apartment data.

Let `R` be a commutative domain with fraction field `K`, at an arbitrary universe
`u`. Let `i : S → G` be the supplied monomorphic inclusion of a commutative
group scheme into an affine group scheme over `K`, with supplied
`C : KPApartmentData i ω`. Fix an apartment point `x`, an actual relative root
`a : relativeRoots i`, and a real depth `r`.

`RootFiltrationModelData R K C x a r` contains:

- An actual generic group `rootGroup` and a homomorphism `inclusion : rootGroup → G`.
- Proof that `inclusion` represents `RelativeRoot.subgroup i a` on **every**
  test scheme over `K`. This includes a scheme monomorphism and equality of the
  represented subgroup functor, rather than just equality on `K`-points.
- An actual `IntegralModel R K rootGroup`. This includes an affine, flat,
  locally finite type group over `R` and its specified generic-fibre isomorphism.
- Smoothness and geometric connectedness of all fibres of that integral model.
- The exact equality
  `model.integralPoints.map (rationalPoints.map inclusion) = C.filtration x a r`.
  Integral points here are the existing image of integral sections under generic
  evaluation and the chosen generic-fibre isomorphism. The equality uses the
  specified generic inclusion into the original ambient group.

An inhabitant therefore supplies a root model with a generic identification,
not an abstract group isomorphic to the filtered point group. The model's
structural affineness and local finite type imply finite type. Geometric
connectedness is explicitly supplied and is not inferred from the point-image
equality.

The theorem `RootFiltrationModelData.filtration_le_integralPoints` assumes an
actual compatible map `φ : U.model.Hom N U.inclusion` to an ambient model `N`.
It rewrites by the supplied integral-point image equality, then uses the
published generic-point naturality theorem `Hom.map_mem_integralPoints` for
each element of that image. It concludes that the exact filtration subgroup is
contained in `N.integralPoints`.

Constructing an inhabitant of this interface is a retained geometric obligation.
A compatible ambient model map is a separate input to the theorem, not a field
of the structure or a consequence of the generic point-image equality. The
interface does not assert that the map of integral models is a closed immersion,
or that its image represents the integral `RelativeRoot.subgroup` for any
supplied split integral torus. In particular, specialization results requiring
that stronger all-test identity over `R` must still establish it explicitly.

For the task over the maximal unramified integers, use
`R = fixedFieldIntegers F`, `K = inertiaFixedField F`, and the apartment data
`B.apartment` of the supplied `B : MaximalUnramified.BuildingData F G`.
The interface itself applies to arbitrary fraction fields and supplied apartment
data; it does not assert a model construction over those more general bases.
