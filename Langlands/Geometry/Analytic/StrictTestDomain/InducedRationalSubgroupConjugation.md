# Conjugation of the original finite-index rational towers

This is an internal construction from the existing original finite-index
rational tower and rational translations. The entry construction is
`OpenSubgroupTransport.FiniteIndexLevel.rationalTowerConjugationIso`, in the
namespace
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction`.
It assembles the existing `translationIso` maps into an isomorphism of actual
rational transport functors and then applies the existing induced-spectrum
functors. No external comparison theorem or arithmetic identification is used.

## Inputs and provenance

Fix a topological group `G`. The subgroup constructions use only this group and
its topology. For the geometric constructions, fix a complete ultrametric
normed field `K`, a presented strict affinoid algebra `P`, and an actual
`RationalSpectralAction G P`. Fix an open subgroup `U`, an invariant rational
presentation `d` for `U`, and an element `g : G`. The field and group share one
arbitrary universe `u`. There are no coefficient objects in this unit, no
normality premise, and no local stable-neighbourhood premise.

The imported `FiniteIndexLevel U` consists of all original open subgroups
`V ≤ U` with nonzero relative index in `U`. It is an inclusion category.
`rationalObject d V` retains `d`'s rational presentation with the original
action restricted to `V`; `rationalArrow d f` is the existing label-one map
for an inclusion `f`. Its induced spectrum is the original balanced quotient
of `G` times the actual local rational spectrum by `V`.

The moved rational presentation is exactly
`(ρ.invariantConjugationEquivalence U g).functor.obj d`.
Its rational data is `ρ.toMonoidHom g • d.obj`, and its operator subgroup is
the actual `g U g⁻¹`. These are the existing conjugation and rational action
constructions. This unit proves the additional finite-level and tower
compatibilities rather than taking those compatibilities as data.

## Original subgroup conjugation

`conjugateOpenSubgroup_mono` proves preservation of subgroup inclusion directly
from the existing inverse-conjugation membership definition.
`conjugateOpenSubgroup_le_iff` proves reflection too by applying conjugation
by `g⁻¹` and using `conjugateOpenSubgroup_inv`.

`relIndex_conjugateOpenSubgroup` proves that simultaneous conjugation leaves
the actual natural-number relative index unchanged for any two open
subgroups. Its proof expresses both conjugate subgroups as comaps under the
same conjugation automorphism, applies Mathlib's `Subgroup.relIndex_comap`,
and cancels map after comap using the automorphism's surjectivity.
`conjugateOpenSubgroup_inf` proves that the original subgroup intersection
is preserved by extensionality and the same membership definition.

`conjugationOrderIso U g` is the resulting order isomorphism from all
`FiniteIndexLevel U` to all `FiniteIndexLevel (conjugateOpenSubgroup U g)`.
Its forward map is the original subgroup conjugation. Its inverse conjugates
by `g⁻¹`, with inclusion and nonzero relative index derived from the proved
laws. Its two inverse laws are actual subgroup equalities, lifted to levels
by subtype extensionality. `conjugationEquivalence U g` is the induced
equivalence of the thin inclusion categories.

`conjugationEquivalence_obj_val` identifies its underlying subgroup exactly.
`conjugationOrderIso_base` transports the original largest level.
`conjugationOrderIso_commonRefinement` identifies the image of each
canonical intersection refinement with the intersection of the images.
`conjugationOrderIso_relIndex` retains the actual relative index between
any two levels, including incomparable ones.

## Original rational tower isomorphism

At a level `V`, `rationalConjugationIso d g V` is exactly the existing
`translationIso V.val g` for the original presentation restricted to `V`.
Its target is the rational object at the conjugate level for the moved
largest-level presentation. Restriction followed by translation and
translation followed by restriction have the same underlying rational data;
the invariance proofs agree by proof irrelevance. The hom has original
label `g` and the inverse has original label `g⁻¹`, as the two label
theorems record.

`rationalConjugationIso_naturality` proves that each original label-one
subgroup map commutes with these translations. Morphisms of the existing
transport category are determined by their retained group labels, so both
composites have label `g`. The natural isomorphism
`rationalTowerConjugationIso d g` therefore has type

`rationalTower d ≅ (conjugationEquivalence U g).functor ⋙ rationalTower d'`,

where `d'` is the moved presentation above. It has all original finite-index
levels and all their original subgroup maps as its source diagram, with
the target diagram reindexed along the actual level equivalence.

## Actual induced spectra and quotient formulas

`inducedSpectrumTowerConjugationIso` postcomposes this natural isomorphism
with `inducedSpectrumFunctor`. Its objects are the actual balanced quotient
spectra with their jointly continuous actions of the whole group `G`.
`inducedSpaceTowerConjugationIso` instead uses
`inducedTopologicalSpaceFunctor`, retaining the same original spaces and
maps after forgetting the actions. These constructions need no stability
premise.

`inducedConjugationHomeomorph d g V` is the homeomorphism of actual balanced
quotients obtained by applying the topological-space functor to
`rationalConjugationIso`. The forward and inverse evaluation theorems identify
its maps with the original `hom.inducedMap` and `inv.inducedMap` respectively.
Its inverse and continuity laws are therefore supplied by the existing
functor and the actual rational isomorphism, through `TopCat.homeoOfIso`.

`inducedConjugationHomeomorph_smul` proves whole-group equivariance.
`inducedConjugationHomeomorph_mk` gives its formula on every original
representative:

`[a,x] ↦ [a * g⁻¹, (rationalConjugationIso d g V).hom.localSpectrumMap x]`.

The second coordinate is the existing actual local spectrum map obtained
from the bounded rational pullback. The first coordinate is the original
inverse-label correction. `ambientMap_inducedConjugationHomeomorph`
proves that the map lies over the identity of the ambient spectrum.

`inducedConjugationHomeomorph_naturality` evaluates the rational naturality
square at an arbitrary original quotient point and applies the existing
induced-map composition law. Thus the square commutes with the original
subgroup quotient maps on both sides. Finally,
`isProperMap_rationalConjugationIso_hom` and its inverse counterpart derive
properness of both original maps from these actual homeomorphisms.

## Remaining scope

This unit varies original finite-index subgroups and transports one fixed
rational presentation and its tower by one group element. It supplies the
geometric conjugation maps, not new compact-function or cohomology maps.
Transport on full coefficient, compact Godement and derived towers, general
rational coverings and charts, analytic or etale realization, arithmetic
Hecke identification and convolution, uniformization, Shimura
specialization, and the Harris comparisons remain separate obligations.
