# The specified generic map of recovered apartment tori

This derived internal unit constructs the generic map of the actual integral
extension from `UnramifiedRecoveredTorusMap` on its prescribed generic tori
and identifies it with its prescribed input morphism.
It composes that module with `IntegralTorusCharacterNaturality.genericFibreMap`
and the conversion `IntegralSplitTorusData.toIntegralTorusData` from
`IntegralSplitTorusConversion`. The direct provider import supplies the same
adapter without the unrelated facet-sign descent interface. All declaration
types and proof bodies are unchanged. It adds no independent literature assertion.

For `genericFibreMap_homToSplitTorus`, let R and K be types in a common universe,
with R a commutative domain, K a field and an R-algebra which is its fraction
field. Supply a group scheme G over K, relative component model data D over R
for G, commutative group schemes S and S' over K with morphisms i and i' into G,
`A : IntegralTorusData D S i`, an explicit splitting proof
`hA : IsSplitTorus A.torus.toGrp`,
`B : IntegralSplitTorusData D.neutral i'`, and a specified morphism
`f : S ⟶ S'`. The theorem states that the generic base change of
`A.homToSplitTorus hA B f`, expressed using both supplied generic
identifications, is exactly f. This conclusion requires no factorization
hypothesis on i and i'. Its proof unfolds these identifications, uses
`fieldHomExtension_generic_comm`, and cancels A's generic isomorphism.
The conversion of B retains its torus and generic identification.

For `apartmentTorusGenericMap` and its comparison theorems, let F be a valued topological field
satisfying `IsNonarchimedeanLocalField F` and put K = `inertiaFixedField F`.
Supply an affine group scheme G over F, a commutative group scheme T over F and
morphism iT into G whose pullback to K is monomorphic on underlying schemes,
an actual `KPApartmentData` D for that upper inclusion and the
maximal-unramified integer valuation, an apartment subset Ω, and
`M : RecoveredApartmentFixerModels D Ω`. Supply a centralizer datum C for the
upper inclusion with the full proof
`hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C`.
Also supply S over F, its inclusion iS into G, a maximal splitness proof
`hiS : IsMaximalSplitTorus iS`, and the specified `f : S ⟶ T` satisfying
`hf : groupHom(f) ≫ iT = iS`. Finally assume connected reductivity
`hG : IsConnectedReductive G` and maximal splitness hiT of the actual pullback
of iT to K. These are additional supplied hypotheses, not fields of M.

`apartmentTorusGenericMap` applies the actual generic-fibre construction to
`M.apartmentTorusMap C hDC hiS hf hG hiT`, expressed on the prescribed generic
tori. Its source is the coefficient pullback of S and its target is the
coefficient pullback of T. The integral source in this construction is the actual
base-changed lower apartment torus and its target is the actual upper neutral
apartment torus converted to `IntegralTorusData`.
`genericFibreMap_apartmentTorusMap` and `apartmentTorusGenericMap_eq` state
that this map equals the coefficient pullback of f. The first is a direct
specialization of the general identity, using the integral splitting already
proved for the source torus; the second unfolds the new specialization.

Both identities hold at every universe and in arbitrary field and residue
characteristic. They supply the exact generic morphism needed by character
restriction comparisons; they assert neither root nonvanishing nor chamber
existence.
