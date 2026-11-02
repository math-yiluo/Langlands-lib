# Full smooth sheaves on actual induced rational spectra

The declarations are in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SpatialSheaves`.

This module specializes the full smooth spatial sheaf equivalence and both
coefficient-natural comparisons to the actual rational quotient Banach spectrum
and its balanced induced spectrum. It retains every original ordinary-open
section and coefficient intertwiner. It also connects this coefficient functor
to the one already used by the rational smooth cohomology construction and
its full compact-function comparison.

The provenance is internal. The module reuses
`InducedRationalSpatialSheaves`, `InducedRationalSmoothCohomology`,
`Sheaf.Equivariant.SmoothSpatialInduction` and
`Sheaf.Equivariant.SmoothSpatialLocallyConstant` by Lean name. It instantiates
their proved constructions on the actual rational spectra and identifies
their original sections and morphisms. It introduces no assumed equivalence,
comparison or new original-literature assertion.

## Actual inputs and size

All carriers in this smooth specialization are in the common universe `u`.
Let `K` be a complete normed ultrametric field, let `P` be a presented strict
affinoid `K`-algebra, let `G` be a topological group, and let
`ρ : RationalSpectralAction G P`. For `X : ρ.OpenSubgroupTransport`, write

- `H = X.subgroup.toSubgroup`, with its inherited topology;
- `S = X.LocalSpectrum`, the actual `BanachSpectrum X.domain.obj.algebra`;
- `T = X.InducedSpectrum = G ×_H S`, with the constructed quotient topology;
- `i = X.inducedUnit`, the map `x ↦ [1,x]`.

The subgroup is open by `X.subgroup.isOpen'`. The action on `S` is the
constructed action from the bounded rational section operators; its joint
continuity is proved in `InducedRationalSpectrum`. The balanced relation and
ambient action are `[gh,x] = [g,hx]` and `a[g,x] = [ag,x]`.
These actual structures supply all spatial-induction inputs.

The coefficient ring `R : Type u` is any commutative ring. Smooth
coefficients range over `Langlands.SmoothRep.{u,u,u} R G`, with their original
module carriers and all original intertwiners. There is no coefficient
topology or finite-dimensionality hypothesis. The sheaf coefficient category
is `ModuleCat.{u} R`. The module asserts no universe-lifting comparison.

There is no normality hypothesis on `H`, or local compactness, total
disconnectedness, compactness or separation hypothesis on these spaces.
The full smooth sheaf equivalence requires no stable-neighbourhood assumption.
The coefficient branch has the single such hypothesis
`HasStableNeighbourhoods H S`.

## Full smooth sheaves and genuine induction

`isLocallyFixedAt_restrict_iff` identifies local fixedness of an arbitrary
section at `x` after unit-chart restriction with local fixedness of the
same ambient section at `i(x)`. Its input is any module-valued transport
presheaf and any section over the image of a local open. The generic proof
uses actual image/preimage neighbourhoods and open-subgroup image/comap.

`isSmoothSheaf_restrict_iff` identifies smoothness of the full local
restriction with smoothness of the entire ambient sheaf. The generic proof
transports local fixed witnesses through the translated charts covering `T`,
conjugating the open subgroups and using the original transport maps.

`smoothRestrict X R` and `smoothInduce X R` are functors between the full
smooth equivariant sheaf categories on `(G,T)` and `(H,S)`. The smoothness
condition is proved for their unchanged ordinary sheaves. No smooth-section
submodule is substituted for the original sheaf.

The two restriction evaluation lemmas identify its underlying ordinary
object and its action on every sheaf morphism. `smoothRestrictForgetIso`
identifies forgetting smoothness with the previously constructed rational
restriction `restrict X (ModuleCat.{u} R)`.

`isSmoothSheaf_induce_iff` proves preservation and reflection of smoothness
for the original rational right Kan extension. The induction evaluation
lemmas identify its ordinary sheaf and, literally, its transport presheaf
and map as

```lean
(unitFunctor X).op.ran.obj F.obj.obj
(unitFunctor X).op.ran.map f.hom.hom
```

The required limits are the actual module limits already supplied by
`InducedRationalSpatialSheaves`; there is no additional completeness input.
`smoothInduceForgetIso` identifies the underlying functor with the original
rational `induce`.

`smoothRestrictionEquivalence X R` has forward functor `smoothRestrict` and
inverse `smoothInduce`. Its triangle identity is inherited from the
constructed generic smooth equivalence.
`smoothRestrictInduceIso` recovers each complete original local smooth
sheaf, and `smoothInduceRestrictIso` recovers each complete ambient smooth
sheaf. Both are natural in every sheaf morphism. Fullness and faithfulness
of both functors are obtained from this equivalence.

## Stable neighbourhoods and full coefficient functors

`hasStableNeighbourhoods_iff` proves

```lean
HasStableNeighbourhoods H S ↔ HasStableNeighbourhoods G T
```

without assuming either side. This specializes the proved stable-neighbourhood
transfer through the actual quotient charts and unit embedding. Under the
local hypothesis, `hasStableNeighbourhoods_induced` supplies the ambient
property. It is an explicit theorem rather than a recursive global instance.

`smoothInducedCoefficientFunctor X R` constructs the full smooth locally
constant coefficient sheaf on `T`, using that derived ambient property.
`smoothLocalCoefficientFunctor X R` first applies the existing arbitrary-ring
smooth restriction along `H ↪ G`, then constructs the full local smooth
locally constant sheaf on `S`. Smooth restriction retains the original
carrier and coefficient maps and has proved pullback smoothness.

The two coefficient forgetful isomorphisms identify these functors with
`SmoothRep.toRep` followed by the full ordinary coefficient functors already
constructed in `InducedRationalSpatialSheaves`. The local forgetful
identification is reflexive: the lifts retain the original functors, and
the functor-composition endpoints agree definitionally.

`smoothRestrictCoefficientNatIso` identifies the induced coefficient functor
followed by smooth restriction with the full local coefficient functor.
For a local open `U`, its forward component pulls every locally constant
section back along `unitOpenHomeomorph X U`; the inverse pulls back along
the inverse homeomorphism. The two evaluation lemmas record these exact
maps. Their compatibility with each subgroup-labelled pullback includes
the unchanged inverse coefficient operator.

`smoothLocalCoefficientFunctor_map_app` evaluates every original intertwiner
pointwise as `s(x) ↦ c(s(x))`. Naturality therefore retains the entire
smooth coefficient category at each fixed rational object.
`smoothInduceCoefficientNatIso` is the converse full comparison. It uses
the actual right Kan induction and the previously proved ambient
reconstruction isomorphism, via the generic smooth coefficient comparison.

## Connection to the existing cohomology coefficient construction

`smoothCohomologySheafFunctorIso` identifies the induced coefficient functor
with `OpenSubgroupTransport.SmoothCohomology.sheafFunctor X`. It explicitly
installs the ambient stable-neighbourhood property just constructed from
the local one. The identification is reflexive: both constructions have
the same full locally constant sheaf and coefficient maps; proof
irrelevance identifies their smoothness witnesses.

`smoothCompactSectionsIso` specializes the existing full compact-function
comparison to this same coefficient functor, with only the local
stable-neighbourhood hypothesis. Its endpoints are the full
`CompactSections.coefficientFunctor X` and the constructed full smooth
sheaf followed by `smoothSheafCompactSections R G T`. Its proof reuses
`SmoothCohomology.compactSectionsIso X` after supplying the derived ambient
property. It retains all compact locally constant functions and their
original diagonal action and coefficient maps.

## Wider scope

These are smooth equivariant sheaves on ordinary opens of actual rational
Banach spectra and their balanced induced spaces. Variation in rational
transport objects, supported Godement and higher derived comparisons,
identification with an analytic or étale site, arithmetic coefficient systems
and level towers, and the Harris specialization remain wider-task obligations.
The compact-section bridge reuses the existing construction; it supplies no
new higher-cohomology or supported-complex comparison. No assertion that the
local stable-neighbourhood hypothesis always holds is made here.
