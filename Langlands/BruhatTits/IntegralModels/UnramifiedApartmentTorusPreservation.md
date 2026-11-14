# Original-residue torus preservation from an unramified apartment

This is an internal derived result toward the prescribed Galois-fixed building
point problem. It specializes the coefficient comparison for smooth integral
models to the actual maximal-unramified extension, derives its generic-torus
bound from the supplied apartment, and discharges its coefficient arithmetic.
It applies in arbitrary universe `u` and in both characteristics.

## Statement and actual maps

`UnramifiedApartmentTorusPreservationStatement` is a closed `Prop` definition.
Let `F` be a nonarchimedean local field, `R = 𝒪[F]`,
`K = inertiaFixedField F`, and `A = fixedFieldIntegers F`. Let `G` be an affine
group scheme over `F`. Supply building data
`C : MaximalUnramified.BuildingData F G_K`, an unramified zero datum `E`, and
any subset `Ω` of `C.Apartment`. Here `G_K` is the actual coefficient base
change of `G`. The building data includes a maximal split torus
`C.i : C.S.toGrp ⟶ G_K` and connected reductivity of `G_K`.

Let `M` and `N` be smooth integral models of `G` over `R`, assume the full
special fibre `M.specialFibre` is connected, and supply an actual integral-model
morphism `φ : M.Hom N (𝟙 G)`. Its generic compatibility is over the identity of
`G`. Assume only the following source inclusion upstairs:

```
E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)
  ≤ M.baseChangeUnramified.integralPoints.
```

`baseChangeUnramified` is `M.baseChange A K`, with the transported original
generic identification. Its integral-point subgroup is the image of actual
`A`-sections in `G_K(K)`. The special fibre is the actual base change along
`R → IsLocalRing.ResidueField R`, and `φ.specialFibreMap` is the base change
of the actual model morphism. The conclusion has three clauses:

- Every maximal torus inclusion `i : T.toGrp ⟶ M.specialFibre` over the
  original residue field remains maximal as `i ≫ φ.specialFibreMap`, with
  exactly the same torus source.
- There exist such an original-residue torus `T` and inclusion `i` with both
  maximalities.
- For every torus `T` over the original residue field and closed subgroup map
  `i : T ⟶ M.specialFibre`, the composite `i ≫ φ.specialFibreMap` is closed.
  This clause includes nonsplit tori.

`IsMaximalTorus` means a genuine closed torus inclusion maximal among all
closed torus factorizations. `IsClosedSubgroup` means a closed immersion of
group schemes. The conclusion uses these predicates, rather than merely
inclusions or maximality of rational-point subgroups. No target connectedness,
nonemptiness or boundedness of `Ω`, or separate kernel hypothesis is assumed.

## Implemented proof

The file installs the actual integer-extension algebra and scalar tower using
`Valuation.HasExtension.instAlgebraInteger` and
`Valuation.HasExtension.instIsScalarTowerInteger`. Locality is the published
`integerToFixedField_isLocalHom`. The arithmetic inputs
`fixedFieldIntegersIsHenselian`, `fixedFieldIntegersIsDVR_of_valuesFromBase`
with `fixedFieldValuesFromBase`, and `fixedFieldResidueIsAlgClosure` make `A`
a Henselian DVR with algebraically closed residue field. The residue algebra
used for the last assertion is the one induced by `residueToFixedField`.
No local-field instance on the noncomplete field `K` is used.

For `isMaximalTorus_specialFibreMap_of_unramified_apartment`, the published
`map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer` puts the image
of the bounded points of `C.S` inside the displayed source subgroup. Composing
with the supplied inclusion bounds this generic maximal split torus in the
actual coefficient pullback of `M`.

There is a universe issue in applying the coefficient theorem: its value group
is in `Type u`, while `MaximalUnramified.valuation F` takes values in
`WithZero (Multiplicative ℤ)`, in `Type 0`. The proof uses the intrinsic
valuation `ValuativeRel.valuation K` for the valuative relation induced by
`fixedFieldValued F`. Its value group is in `Type u`. By definition the
normalized valuation is its composition with the order monoid isomorphism
`MaximalUnramified.valueGroupEquiv F`. The proof establishes their
`Valuation.IsEquiv` relation using `map_le_map_iff`.
`characterValuationKernel_eq_of_isEquiv` then rewrites the bound for the
intrinsic valuation. The same equivalence transports
`SpecialTorusIntegralModel.valuation_units_eq_one` to the required unit values.

With these concrete inputs, apply
`IntegralModel.Hom.isMaximalTorus_specialFibreMap_of_coefficient_bounded` to
`C.isConnectedReductive`, `C.isMaximalSplitTorus`, and the rewritten bound.
That theorem constructs a common maximal torus after coefficient extension,
uses the canonical residue-comparison square, and applies geometric conjugacy
and reflection to the original-residue map. A common geometric torus is an
output of its construction, not an extra premise here.

For `exists_maximalTorus_specialFibreMap_of_unramified_apartment`, smoothness
and affineness of the original source special fibre follow by base change.
`maximalTorusExistence` supplies an original-residue maximal torus; the preceding
result gives maximality of its composite. This does not descend a particular
chosen torus from the algebraically closed residue field upstairs.

For `isClosedSubgroup_specialFibreMap_of_unramified_apartment`, affineness and
local finite type of the source special fibre also follow by base change.
A torus has its canonical commutative group structure. Apply
`IsClosedSubgroup.comp_of_maximalTorus_images` to that commutative source and
the universal maximality result. This published helper extends the closed
torus to a maximal torus over the same field, then composes the resulting
closed inclusions. `unramifiedApartmentTorusPreservation` assembles the three
proved clauses. Only this final packaging theorem uses a finite
`maxHeartbeats 600000`; the four substantive helpers use the default limit.

For supplied relative component models, the additional helper
`RelativeComponentModelHom.preservesTori_of_unramified_apartment` applies the
closedness result to `φ.neutral`. Source connectedness follows from
`neutral_connectedFibres` through
`IntegralModel.hasConnectedSpecialFibre_of_hasConnectedFibres`. Smoothness is
part of each component model's data. The conclusion `φ.PreservesTori`
quantifies all closed tori and uses the actual `φ.neutralSpecialFibreMap`;
it is the torus preamble of KP Axiom 4.1.22 on these supplied models.

## Provenance and remaining scope

The provenance is the composition of Library declarations in
`CoefficientSpecialFibreTorus`, `MaximalTorusImageSplitLift`,
`ConnectedFibreDescent`, and `UnramifiedModelKernelTorus`, together with the
arithmetic, valuation, actual model and special-fibre constructions named
above. This module makes no new claim of a direct transcription from a
literature source. The generic torus bound and all coefficient arithmetic are
proved from the actual unramified setting; the models, their identity-generic
map, the building and zero data, and the source inclusion remain supplied.

This result does not construct coherent descended building models or the
facet-parabolic and segment comparisons, lift a prescribed residue torus over
the valuation ring, establish a smooth connected unipotent kernel, or locate
the prescribed fixed point in a special apartment. It therefore leaves
`UnramifiedFixedPointSplitTorusStatement` open. It uses none of the four barred
building-descent statements or their consumers.
