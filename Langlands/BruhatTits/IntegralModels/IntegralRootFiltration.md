# Integral root-filtration models from a compatible integral split torus

This internal construction combines `IntegralModel.SplitRoot` with
`GenericRootFixerIntersection`. Work over a domain `R : Type u` and its
specified fraction field `K : Type u`. Let `N : IntegralModel R K G` be
smooth, let `i : S.toGrp ⟶ G` be a maximal split torus of an affine connected
reductive generic group, and let `C : KPApartmentData i ω` be supplied.
The valuation `v` used below is arbitrary and need not define `ω`.

`IntegralSplitTorusData N i` supplies an actual split torus over `R`, a map
from it into `N.group`, an isomorphism from its generic fibre to `S`, and
the commuting generic inclusion square. The structure asserts no existence
of an integral torus. It imposes no integral closed-immersion hypothesis on
the torus map.

For every nonzero generic character `a`, `integralCharacter a` is an
actual integral character. It is constructed using the published character
lattice base-change equivalence for a split torus between integral-domain
spectra and the supplied generic torus isomorphism.
`generic_integralCharacter` proves exact generic recovery and
`integralCharacter_ne_zero` proves nonvanishing. The all-test identity
`generic_rootFunctor_eq` uses the commuting square and the existing
transport theorem for the full intrinsic root functor.

`rootGroup`, `rootInclusion`, and `rootModel` apply the published integral
root construction to this integral character. The generic inclusion
represents the full intrinsic root functor for `i` and `a`, on every scheme
test. `rootModelMap` is an actual compatible map into `N`, and
`rootModelMap_isClosedSubgroup` proves that its integral map is closed.
The resulting model is smooth affine with geometrically connected fibres.
`rootModel_integralPoints_eq` identifies its actual generic point image
with `N.integralPoints ∩ rootGroupPoints i a`.

Now suppose `Ω` is a nonempty apartment subset whose image under every
real affine functional is bounded above, and suppose the actual ambient
point identity

`N.integralPoints = characterValuationKernel v G ∩
C.pointwiseFixer (C.apartmentMap '' Ω)`

is supplied. For any reference point `x` and relative root `a`,
`rootModel_integralPoints_eq_filtration` identifies the constructed root
model's point image with
`C.filtration x a (C.rootFixerDepth a x Ω)`. It uses the full
root/fixer intersection theorem and its bounded-set filtration formula;
no extra apartment axiom, topology, local-field structure at `K`, or
root-filtration image premise is imposed.

`rootFiltrationModelData` packages the actual generic representative,
smooth affine integral model, geometrically connected fibres and proved
point-image equality into the existing `RootFiltrationModelData`.
`rootFiltrationModelMap` supplies its actual compatible ambient integral
map, namely the closed map `rootModelMap`.

The provenance is internal. The new `GenericRootFixerIntersection` helper
and its paired Markdown are included for review and integration together
with this unit. The primary construction composes that helper with published
split-character base change, all-test root transport and integral root
representability. It supplies the root-model part of
the parahoric construction once the explicit ambient model and compatible
integral split torus have been given. It constructs neither of those
inputs, no integral maximal torus model, and no equality with an arbitrary
zero subgroup. It does not prove `UnramifiedParahoricModelStatement`.
