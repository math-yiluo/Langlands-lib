# Spatial sheaves on actual induced rational spectra

The declarations are in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SpatialSheaves`.

This module specializes the constructed spatial equivalence to the **actual
rational quotient Banach spectrum** and its balanced induced spectrum. It
constructs restriction and genuine right Kan induction on all ordinary-open
equivariant sheaves, with both natural inverse isomorphisms. It also identifies
the full locally constant coefficient sheaves in both directions, naturally in
every original coefficient intertwiner.

The provenance is internal. The definitions reuse
`InducedRationalSpectrum`, `InducedRationalCharts`,
`Sheaf.Equivariant.SpatialInduction` and
`Sheaf.Equivariant.SpatialLocallyConstant` by Lean name. The generic geometric
and dense-subsite proofs are reused; their actual space and action inputs are
instantiated here. No new original-literature assertion or assumed comparison
is introduced.

## Actual spaces, actions and size

Let `K : Type u` be a complete normed ultrametric field, let `P` be a presented
strict affinoid `K`-algebra, and let
`ρ : RationalSpectralAction G P`. The group `G : Type v` has its specified
topological group structure. For an object `X : ρ.OpenSubgroupTransport`, put

- `H = X.subgroup.toSubgroup`, with its inherited subgroup topology;
- `S = X.LocalSpectrum`, the actual
  `BanachSpectrum X.domain.obj.algebra`, with the topology of this spectrum;
- `T = X.InducedSpectrum = G ×_H S`, the constructed balanced quotient with
  the quotient topology;
- `i = X.inducedUnit : S → T`, given by `x ↦ [1,x]`.

The action on `S` is the existing action induced by the bounded rational
section operators. Its joint continuity is already proved in
`InducedRationalSpectrum`. The open-subgroup proof is exactly
`X.subgroup.isOpen'`. Consequently all hypotheses of spatial induction hold
for these inputs. The quotient relation and actions have the conventions

\[
 [gh,x]=[g,hx],\qquad a[g,x]=[ag,x].
\]

The general branch retains independent field, group, category-object and
category-morphism universes `u,v,a,b`. Its coefficient category is any
`A : Type a` with `Category.{b} A`. Restriction needs no coefficient limits.
The inverse and the equivalence explicitly require

```lean
∀ U : (ActionOpens G X.InducedSpectrum)ᵒᵖ,
  HasLimitsOfShape (StructuredArrow U (unitFunctor X).op) A
```

These are the actual limits for pointwise right Kan extension. They are not
assumed sheaf equivalences or cohomology groups.

The openwise homeomorphisms and linear equivalences retain independent
`u,v,r,w`, with `R : Type r` a commutative ring and `M : Type w` an arbitrary
`R`-module. The categorical coefficient branch explicitly puts the field and
group in universe `u`, retains independent ring and module universes `r,w`,
and uses `ModuleCat.{max u w} R` on both spaces. It claims no comparison
between different module-category universes.

There is no coefficient topology, finite-dimensionality assumption, subgroup
normality, local compactness or total disconnectedness assumption on `G`, or
stable-neighbourhood assumption on either spectrum.

## Actual opens, labels and restriction

`unitFunctor X` is the genuine unit-chart transport functor

\[
 \operatorname{ActionOpens}(H,S)\longrightarrow
 \operatorname{ActionOpens}(G,T).
\]

`unitOpen_carrier` identifies its object at an arbitrary local open `U`
with `i '' U`. Its openness is the one supplied by the actual open unit
embedding. `mem_unitOpen` identifies membership of `i(x)` with membership of
`x` in `U`. `unitOpen_top` identifies the image of the whole local spectrum
with `X.inducedChartDomain 1`, the existing distinguished rational chart.

On a transport arrow with label `h : H`, the functor keeps that same label,
coerced into `G`; `unitFunctor_map_label` records this fact. In particular,
labels are retained even if their actions agree on points.

`chartPreimage X g U` is the inverse image of an arbitrary ambient open
under `X.inducedChart g`, with its actual spectrum topology.
`mem_chartPreimage` gives this membership formula.
`chartArrow X g U` maps its unit-chart image into `U` with label exactly `g`,
as recorded by `chartArrow_label`. These are the specialized translated
chart arrows underlying the generic cover-density proof. All opens, including
the empty open, are retained.

`restrict X A` goes from full `G`-equivariant sheaves on `T` to full
`H`-equivariant sheaves on `S`. The categories are the existing full
categories `TopologicalSheaf`, defined by the ordinary-open sheaf condition
on the underlying transport presheaf. Their morphisms are all natural
transformations.

The underlying presheaf is literally `(unitFunctor X).op ⋙ F.obj`.
The four evaluation lemmas identify that functor, its value at each open,
its map at each subgroup-labelled arrow, and its component at every sheaf
morphism. The proofs are definitional equalities. Fullness and faithfulness
come from the generic dense-subsite comparison, with no limit hypothesis
and no false assertion that the unit transport functor is globally full.

## Genuine induction and the full equivalence

Under the displayed limit hypothesis, `induce X A` is the constructed
spatial right Kan extension. `induce_obj_obj` identifies its underlying
presheaf with

```lean
(unitFunctor X).op.ran.obj F.obj
```

and `induce_map_hom` identifies its action on every morphism with the same
right Kan functor. The sheaf property is supplied by the existing
cocontinuous dense-subsite construction, not supplied as additional input.

`restrictionEquivalence X A` is an equivalence between all ambient and all
subgroup equivariant sheaves on these actual two spaces. Its forward and
inverse functors are exactly `restrict` and `induce`. Its counit is
`restrictInduceIso`, identifying `induce ⋙ restrict` with the identity on
local sheaves. Its inverse unit is `induceRestrictIso`, identifying
`restrict ⋙ induce` with the identity on ambient sheaves. These are natural
isomorphisms of full categories.

## Full coefficient sheaves and original maps

`unitOpenHomeomorph X U` is the actual homeomorphism from an arbitrary local
open onto `i '' U`. Its forward map has underlying point `i(x)`, as stated
by `unitOpenHomeomorph_apply_coe`.

`unitSectionsLinearEquiv X U` pulls back by this homeomorphism on **all**
locally constant functions, with the inverse given by pullback along the
inverse homeomorphism. Both evaluation formulas are recorded. The inverse
laws and linearity are inherited from the constructed generic equivalence.

For an ambient representation `τ : Representation R G M`, a transport
arrow `f : U ⟶ V` has full pullback

\[
 s\longmapsto\bigl(x\longmapsto
   \tau(f.\mathrm{label}^{-1})s(f.\mathrm{label}\,x)\bigr).
\]

`unitSectionsLinearEquiv_pullback` proves that the comparison commutes with
this complete map, including the original inverse coefficient operator.
The local coefficient representation is precisely
`τ.comp X.subgroup.toSubgroup.subtype`.
`unitSectionsLinearEquiv_map` proves compatibility with any original
coefficient linear map, by pointwise equality.

In the categorical branch,
`inducedCoefficientFunctor X R` is the full ordinary-open locally constant
sheaf functor on `T`, with source `Rep.{w} R G`.
`localCoefficientFunctor X R` first restricts that original representation
along the subgroup inclusion and then constructs the full sheaf on `S`.
It uses the same carrier and every original coefficient map:
`localCoefficientFunctor_map_app` evaluates such a map as `s(x) ↦ c(s(x))`.
There is no replacement by a smooth-vector submodule.

`restrictCoefficientNatIso` identifies ambient coefficients followed by
restriction with this full local coefficient functor. Its forward and inverse
component evaluation lemmas give the actual homeomorphism pullbacks.
Naturality includes every ambient representation intertwiner.

`unitChartModuleLimits` constructs the required limits using
`ModuleCat.hasLimitsOfShape` for the actual structured-arrow categories.
Thus the coefficient branch needs no unprovided limit hypothesis.
`induceCoefficientNatIso` identifies local coefficients followed by genuine
spatial induction with the full ambient coefficient functor. It specializes
the constructed generic natural isomorphism, which composes the inverse
unit-chart coefficient comparison with the ambient reconstruction
isomorphism. The converse therefore uses the actual right Kan inverse.

## Scope retained for the wider task

This is a construction on ordinary opens of the actual rational quotient
Banach spectra and their balanced induced spaces. It does not identify them
with an étale site or with Harris's arithmetic spaces. Smooth spatial
equivalence, compact support, supported Godement and derived comparisons,
higher cohomology, variation in rational transport objects, arithmetic
coefficient systems and towers, and the Harris specialization remain
separate obligations of the wider task. The coefficient naturality here is
for all intertwiners at each fixed rational transport object `X`.
