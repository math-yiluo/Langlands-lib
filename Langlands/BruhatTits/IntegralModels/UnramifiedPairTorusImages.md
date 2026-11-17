# Original-residue maximal-torus images from a full pair-fixer model

This is an internal supporting result for Task 6009. It constructs bounded
maximal split torus data in the actual neutral component from a bound on the
full model, then uses coefficient comparison to preserve every maximal torus
over the original residue field. All models, the building datum, the model
comparison and the valid target reductive quotient remain supplied.

## Statement and scope

`Langlands.BruhatTits.IntegralModels.UnramifiedPairTorusImagesStatement`
is a proposition in arbitrary universe `u`; its proof is
`unramifiedPairTorusImages`. Let `F` be a nonarchimedean local field,
`R = 𝒪[F]`, `k = 𝓀[F]`, `K = inertiaFixedField F`, and
`A = fixedFieldIntegers F`. Supply an affine `F`-group scheme `G`, an actual
`MaximalUnramified.BuildingData F G_K` called `B`, and
`D : RelativeComponentModelData R F G`. The building datum includes a maximal
split apartment torus and connected reductivity of `G_K`. The model datum
includes actual smooth affine full and neutral models, their compatible
inclusion, and the relative identity-component assertion.

For any points `y₁,y₂` of `B.ReducedBuilding`, assume only the subgroup inclusion

```
characterValuationKernel (MaximalUnramified.valuation F) G_K
  ∩ B.pointwiseFixer {y₁,y₂}
    ≤ D.full.baseChangeUnramified.integralPoints.
```

Then there is a commutative `K`-group scheme `T` and a map `i : T.toGrp ⟶ G_K`
which is a maximal split torus and whose character-valuation kernel maps into
`D.neutral.baseChangeUnramified.integralPoints`.

Further, supply any `E : RelativeComponentModelData R F G`, actual compatible
`ψ : RelativeComponentModelHom D E`, and `Q : SpecialFibreQuotientData E` with
`Q.IsReductiveQuotient`. This validity asserts that the specified radical is
the smooth connected unipotent radical, that the displayed projection is its
represented fppf quotient, and that the quotient is connected reductive.
For every maximal torus `i₀ : T₀.toGrp ⟶ D.neutral.specialFibre` over the original
field `k`, both

```
i₀ ≫ ψ.neutralSpecialFibreMap
i₀ ≫ ψ.neutralSpecialFibreMap ≫ Q.projection
```

are maximal tori, with the same source `T₀`. The first conclusion is also
available without `Q` or quotient validity, for any smooth target integral
model and any identity-generic map from `D.neutral` to it. These are assertions
about actual scheme homomorphisms and full maximal tori, including nonsplit
tori over `k`.

The endpoints may coincide and need not be Galois fixed. No local-field
structure on `K`, characteristic restriction, equality of the full and neutral
integral-point groups, or neutral apartment-fixer formula is assumed.

## Integral split-torus units

`IntegralSplitTorusData.map_characterValuationKernel_le_integralPoints`
works over an arbitrary integral domain with specified fraction field. The
valuation must have that domain as its valuation ring. For a closed integral
split torus with its specified generic identification, its prescribed generic
torus's character-valuation kernel maps into the model's integral points.

The proof turns the commutative generic isomorphism into an isomorphism of
group schemes, carries a kernel point through its inverse using functoriality
of the character-valuation kernel, and applies
`map_genericHom_mem_integralPoints_of_split_characterKernel` from
`IntegralModel.ResidueSplitTorusGenericLift`. The `generic_comm` field identifies
the generic inclusion with the prescribed torus map. The two induced point
maps cancel by the inverse-homomorphism identity of the actual isomorphism.
Thus no equality between generic and residue split ranks is used.

## Construction in the neutral model

`exists_maximalSplitTorus_units_le_unramifiedNeutral` applies
`exists_pairApartmentTorusData` from `UnramifiedPairApartmentTorus` to the full
model after coefficient extension. That published construction chooses an
actual translated common apartment for the two points and a closed integral
split torus in the full model. Its prescribed generic map is the apartment
torus inclusion followed by the translating point's inner automorphism, so
`PairApartmentTorusData.generic_isMaximalSplitTorus` supplies maximal splitness.

The actual coefficient extension `D.baseChange A K` still has its actual
relative identity component. A split integral torus has geometrically
connected fibres; `IntegralSplitTorusData.factorNeutral` from
`UnramifiedNeutralRoots` therefore factors its entire integral group-scheme
map through that component. The construction retains the original generic
map and generic identification. `factorNeutral_isClosedSubgroup` retains
closedness of the integral inclusion. Applying the preceding units lemma
with `MaximalUnramified.valuation_le_one_iff_mem_range` puts the prescribed
generic torus's units in the neutral model.

This is a factorization of the connected integral torus, rather than a
replacement of the full pair-fixer bound by a neutral point-group equality.

## Original-residue images and the target quotient

`isMaximalTorus_specialFibreMap_of_unramified_full_pair` obtains connectedness
of the actual source neutral residue fibre from its connected fibres using
`IntegralModel.ConnectedFibreDescent`. Its smoothness is part of `D`.
It applies `IntegralModel.Hom.isMaximalTorus_specialFibreMap_of_coefficient_bounded`
from `CoefficientSpecialFibreTorus` to the constructed bounded maximal split
torus upstairs. The local unramified coefficient ring is a Henselian DVR with
algebraically closed residue field, and its residue map extends the original
residue field. The canonical integer valuation is equivalent to the intrinsic
valuation on `K`; the proof uses `MaximalUnramified.valueGroupEquiv` to transfer
the kernel bound. `SpecialTorusIntegralModel.valuation_units_eq_one`, from
`SpecialTorusIntegralModelReduction`, supplies the coefficient-units condition.

The coefficient theorem constructs a common torus over the algebraically
closed residue extension and uses geometric conjugacy and reflection to prove
maximality for every prescribed torus over the original residue field. The
result here accordingly concerns every original-residue maximal torus, not
only a chosen geometric torus.

`RelativeComponentModelHom.isMaximalTorus_quotientMap_of_unramified_full_pair`
then applies `IsMaximalTorus.comp_of_perfect_field_unipotent_kernel` from
`Torus.UnipotentQuotientMaximal`. The field `k` is finite and hence perfect.
The validity of `Q` supplies the smooth connected unipotent radical and its
fppf quotient. Affineness and finite type of the target neutral residue fibre
come from its smooth affine model by actual base change; smoothness of the
quotient comes from its connected reductivity. Associativity identifies the
resulting composite with the displayed quotient map. The final theorem
packages the bounded-torus construction and both maximality conclusions.

## Provenance and remaining obligations

The result is an internal composition of the named Library inputs; it claims
no separate translation of a literature theorem. The substantive new step
is the passage from a full pair-fixer inclusion to a bounded maximal split
torus in the actual neutral model, followed by application to the original
residue-field comparison and actual target quotient.

The module supplies neither the building models nor their pair-fixer bound,
comparison, or quotient validity. It proves no absence of proper rational
parabolics and constructs no maximal split torus over `F` with a prescribed
point-fixing property. In particular, the constructed torus is over `K`;
it is not asserted to descend to `F`. A reference integral source, its generic
`F`-maximal split comparison, a maximal split residue-quotient map, and the
other geometric hypotheses of `ResidueSplitTorusGenericLift` remain necessary
for that application. The main
`UnramifiedFixedPointSplitTorusStatement` remains a separate obligation.

The local coefficient, residue and valuation instances have explicit names
unique to this module. This allows the pair-torus results to be imported
together with the recovered apartment-torus construction; their definitions,
mathematical statements and proof bodies are unchanged.
