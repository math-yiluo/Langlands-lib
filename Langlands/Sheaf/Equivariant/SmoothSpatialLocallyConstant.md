# Full smooth locally constant sheaves under spatial induction

The namespace is
`Langlands.Sheaf.Equivariant.SpatialInduction`.
This internal construction proves stable-neighbourhood transfer between the
actual balanced quotient `Space H X` and its local space `X`, and constructs
both coefficient-natural comparison isomorphisms for their full smooth
locally constant sheaves. The inverse spatial functor remains the genuine
right Kan extension.

The provenance is internal. The balanced quotient, its open translated charts
and unit embedding come from `Topology.GroupAction.InducedSpace` and
`InducedCharts`. `SmoothSpatialInduction` supplies the open subgroup image,
the smooth spatial functors and their inverse natural isomorphisms.
`SpatialLocallyConstant` supplies the full section-module and coefficient-map
comparisons. `LocallyConstantSmooth` proves smoothness of the full locally
constant sheaf using stable neighbourhoods and smooth coefficients.
`Representation.Induction.OpenAdjunction.smoothRestriction` restricts the
original smooth coefficient representation and all its morphisms. No new
original-literature assertion is made here.

All ring, group, space and coefficient-module carriers lie in the common
universe `u`, following the existing smooth sheaf framework. The assumptions
are a topological group `G`, an open subgroup `H`, and a topological space `X`
with jointly continuous `H`-action. The coefficient ring `R` is an arbitrary
commutative ring. Coefficients have no topology and need not be finite
dimensional. No normality, local compactness, total disconnectedness,
compactness or separation hypothesis is imposed. No universe-lifting
comparison is constructed.

`HasStableNeighbourhoods H X` says that each open neighbourhood of a point
contains an open neighbourhood stable under some open subgroup of `H`.
The first three declarations prove transfer of this property in both
directions, without coefficient data.

For `hasStableNeighbourhoods_induced`, represent an arbitrary quotient point
as `[g,x]`. Pull the given ambient open back through the actual translated
chart `y ↦ [g,y]`. Choose a stable open `V` and open subgroup `K` in this
preimage. The new neighbourhood is the actual open chart image `chart g '' V`.
Its stabilizing open subgroup is the preimage of `openSubgroupImage K` under
conjugation `k ↦ g⁻¹ k g`, namely `g K g⁻¹` inside `G`. Conjugation is continuous,
so this subgroup is open. If `g⁻¹ k g = h` with `h ∈ K`, the identity
`k g = g h` and the balanced quotient identity identify `k • [g,y]` with
`[g,h • y]`. This proves stability of the constructed neighbourhood.

For `hasStableNeighbourhoods_local`, apply ambient stable neighbourhoods at
`[1,x]` inside the open unit image of the given local open. Pull the resulting
neighbourhood back through the continuous unit embedding. Pull the ambient
open subgroup back through `H.subtype`, giving the actual subgroup intersection
with `H`, with inherited topology. Unit injectivity proves containment in the
original local open, and unit equivariance proves stability.
`hasStableNeighbourhoods_iff` assembles these implications as

```text
HasStableNeighbourhoods H X ↔ HasStableNeighbourhoods G (Space H X).
```

The remaining declarations assume only the local stable-neighbourhood property.
`smoothLocallyConstantFunctor` applies the original
`LocallyConstantSheaf.smoothFunctor` to the ambient space using the newly proved
ambient property. Thus its sections are all the original locally constant
functions, and its maps are all the original pointwise coefficient intertwiners.
`smoothLocallyConstantFunctorForgetIso` identifies its composite with the
smooth inclusion with

```text
SmoothRep.toRep ⋙ LocallyConstantSheaf.functor R G (Space H X).
```

The coefficient restriction is exactly `Langlands.Induction.smoothRestriction`.
It retains the coefficient carrier and every intertwiner, restricts the action
along `H.subtype`, and obtains smoothness by continuous pullback.
`smoothRestrictLocallyConstantIso` lifts the existing full unit-chart sheaf
comparison through the full smooth subcategory. For a local transport open `U`,
the forward and inverse section maps are the literal pullbacks

```text
s ↦ (x ↦ s (unitOpenHomeomorph U x)),
t ↦ (z ↦ t ((unitOpenHomeomorph U).symm z)).
```

The two evaluation lemmas state these formulas for the unchanged coefficient
carrier. `smoothRestrictLocallyConstantNatIso` proves naturality in every
original smooth coefficient morphism by reducing to the ordinary coefficient
comparison through full-subcategory morphism extensionality. Its endpoints are

```text
smoothLocallyConstantFunctor ⋙ smoothRestrict
  ≅ smoothRestriction R H ⋙ LocallyConstantSheaf.smoothFunctor R H X.
```

`smoothInduceLocallyConstantNatIso` gives the converse comparison

```text
(smoothRestriction R H ⋙ LocallyConstantSheaf.smoothFunctor R H X)
    ⋙ smoothInduce
  ≅ smoothLocallyConstantFunctor.
```

Its implemented map first applies genuine smooth right Kan induction to the
inverse restriction comparison, then applies the existing
`smoothInduceRestrictIso` reconstruction on ambient smooth sheaves. Associators
and the right unitor give the displayed functor endpoints.
`smoothInduceLocallyConstantIso` is its component at an arbitrary smooth
coefficient representation. Both constructions retain the entire sheaves and
all coefficient maps; no submodule of specially chosen sections replaces them.

This unit concerns ordinary-open equivariant smooth sheaves on the actual
balanced quotient. Rational specialization and variation, compact support,
supported Godement and higher derived comparisons, analytic or etale
identification, arithmetic level towers and the Harris specialization remain
obligations of the wider framework.
