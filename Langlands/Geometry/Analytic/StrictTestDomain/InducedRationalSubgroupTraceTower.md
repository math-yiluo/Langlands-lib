# Original compact pullback and trace towers at finite rational levels

This is an internal categorical assembly of the existing original induced
rational spectra, their finite-index subgroup maps, and the compact-function
pullbacks and traces. The entry construction is
`OpenSubgroupTransport.FiniteIndexLevel.compactTraceTower` in the namespace
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction`.
It uses `InducedRationalSubgroupTower` for the actual level category and its
geometry, `InducedRationalSubgroupTrace` for the original coefficient maps, and
`InducedRationalSubgroupTransitivity` for their composition laws. No external
comparison theorem is an input or a conclusion of this unit.

## Inputs and coefficient scope

Fix a complete ultrametric normed field `K`, a presented strict affinoid algebra
`P`, a topological group `G`, and a `RationalSpectralAction G P`. Fix an open
subgroup `U` and an actual invariant rational domain `d` for `U`. The coefficient
ring `R` is any commutative ring. The field, group, coefficient ring and
coefficient modules share one arbitrary universe `u`.

The index category is the existing `FiniteIndexLevel U`: all original open
subgroups `V ≤ U` with nonzero relative index in `U`, with a morphism for each
inclusion. It is nonempty and cofiltered by actual subgroup intersections.
`rationalObject d V` retains the rational presentation of `d` with the
restricted original action. Its induced spectrum is the actual balanced
quotient of `G` times that local rational spectrum by `V`.
`rationalArrow d f`, for `f : V ⟶ W`, is the original label-one subgroup map.
Its covering property, properness, finite literal fibers, and fiber degree
`V.val.toSubgroup.relIndex W.val.toSubgroup` are already derived from these
levels. No normality assumption is needed.

Both towers below retain the entire category `SmoothRep.{u,u,u} R G`, all its
coefficient objects, and all its intertwiners. A tower object is the existing
`CompactSections.coefficientFunctor (rationalObject d V)`: compactly supported
locally constant functions valued in the original coefficient module, with
the original diagonal smooth `G` action. In particular these objects and maps
do not require local stable neighbourhoods or Godement constructions.

## Original pullbacks and traces

`compactPullbackTower d R` is contravariant in subgroup inclusions. Its
transition for `f : V ⟶ W` is exactly
`subgroupRestrictionCompactSupportPullbackNatTrans`, so at a coefficient
object `M` it takes a compact function `s` on the `W` spectrum to
`s ∘ (rationalArrow d f).inducedMap`. The properness of this original map
ensures compact support. Its identity law follows pointwise from the
original induced-map identity. Its composition law is the proved original
compact-pullback composition law.

`compactTraceTower d R` is covariant in the same inclusions. Its transition
is exactly `subgroupRestrictionCompactSupportTraceNatTrans`. The theorem
`compactTraceTower_map_apply` identifies its value at `M`, a compact function
`s` on the `V` spectrum, and a point `y` of the `W` spectrum with

`fiberSum (rationalArrow d f).inducedMap s.val y`.

Thus the map sums `s` over the entire literal original fiber above `y`.
The existing finite-covering trace proves local constancy, compact support,
linearity, equivariance and coefficient naturality. The finite-fiber instance
used in the formulas is derived from `finite_rationalArrow_fiber`; it is not
an additional premise. The identity law reduces the literal induced map to
`id` and uses the singleton-fiber sum. The composition law uses the already
proved original compact trace transitivity, in the order `V → W → Z`.

The object and transition theorems `compactPullbackTower_obj`,
`compactTraceTower_obj`, `compactPullbackTower_map` and `compactTraceTower_map`
are definitional identifications with these original coefficient functors and
maps.

`compactPullbackTrace_degree` proves, as an equality of natural
transformations on the full coefficient category,

`pullback(f) ≫ trace(f) = (V.relIndex W) • 𝟙`.

Both sides are endomorphisms of the coefficient functor at `W`.
The proof evaluates at every coefficient, section and point and applies the
existing original-fiber degree identity. The scalar is a natural-number
multiple in the additive morphism group. The trace is unnormalized: there is
no division by the index and no invertibility hypothesis on it in `R`.

## Whole-group invariants

`invariantCompactPullbackTower` and `invariantCompactTraceTower` postcompose
these towers with `smoothInvariants R G`. Their objects are functors from the
same full smooth coefficient category to `ModuleCat R`. They take invariants
under the entire original group `G`.

`invariantCompactTraceTower_map_apply` is the same literal fiber sum on the
underlying invariant compact function. `invariantCompactPullbackTrace_degree`
proves the same relative-index identity as an equality of natural
transformations of module-valued coefficient functors. Its proof evaluates
inside the fixed submodule and uses the original pointwise degree identity.
No exactness or homology-preservation property of invariants is assumed.

## Canonical intersection spans

For any two levels `V,W`, let `T = commonRefinement V W`, the original open
subgroup intersection. `commonRefinementCorrespondence d R V W` is the
natural transformation obtained by pulling back along `T → V` and tracing
along `T → W`. It acts from compact functions at `V` to compact functions at
`W` for every original coefficient.

`commonRefinementCorrespondence_naturality` records that every coefficient
intertwiner commutes with this operator. The point formula
`commonRefinementCorrespondence_apply` sums, over the entire fiber of
`T → W` above `y`, the value of `s` at the image of each summand point under
`T → V`. The equation uses the original two `rationalArrow` maps, without a
replacement fiber or a selected set of coset representatives.
`invariantCommonRefinementCorrespondence` applies whole-group invariants to
the same natural transformation. These are actual intersection-span
operators; this unit does not identify them with an arithmetic Hecke
correspondence or prove general correspondence convolution laws.

## Agreement with the stable cohomology tower and remaining scope

Only the last two theorems assume
`HasStableNeighbourhoods` for the original largest-subgroup action on the
local spectrum of `d`. With that premise the previously constructed
`compactFunctionsTower` and `invariantCompactFunctionsTower` exist.
`compactPullbackTower_eq_compactFunctionsTower` and its invariant analogue
are definitional equalities: the independent pullback towers here have
exactly the original objects and maps used there.

This construction varies finite-index subgroups of one fixed invariant
rational presentation. It supplies traces and intersection operators on
compact functions and their whole-group invariants. General rational
coverings and charts, analytic or etale realizations, trace transport on
Godement or higher derived cohomology, arithmetic Hecke identification,
uniformization, Shimura specialization, and the Harris comparisons remain
separate obligations. In particular no higher cohomology trace or comparison
is asserted by the present compact-function tower.
