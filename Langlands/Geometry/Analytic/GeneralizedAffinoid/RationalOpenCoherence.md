# The actual locally ringed spectrum functor

Author: Worker 36.

This module proves identity and composition for the concrete ordinary-open
pullbacks and the sheaf and locally ringed-space morphisms of
[RationalOpenPullback](RationalOpenPullback.md) and
[RationalOpenMorphism](RationalOpenMorphism.md). It packages the latter as
`RationalChart.locallyRingedSpaceFunctor`.

The field `K` is complete, normed and ultrametric. The objects are the actual
positive-polyradius quotient presentations `PresentedAffinoidAlgebra K`;
the arrows are all bounded `K`-algebra maps. In particular the construction
does not require a nontrivial valuation, reduced algebras, nonempty spectra,
strict radii, or a selected class of coefficient maps.

For a bounded map `φ : A → B`, write `fφ : M(B) → M(A)` for its continuous
bounded-seminorm spectrum map and `φ*` for its constructed section pullback.
For an ordinary open `U` of `M(A)`, the section algebra consists of compatible
families of actual rational quotient elements on all rational charts contained
in `U`. The laws are equalities in those algebras, including their nilpotents.

## Identity on concrete sections

`OpenSections.pullback_id` states, for every `U` and every concrete section `s`,

```
(id_A)* s = s.
```

The proof compares each actual rational quotient component at a chart `e`.
The local formula for the constructed pullback identifies that component with
restriction along the inverse of `pullbackIdIso e`, applied to the coefficient
transport of `s(e)`. The proved identity-comparison equation identifies that
transport with restriction along the forward comparison. The inverse law of
the chart isomorphism then gives the original quotient element.

## Composition on concrete sections

`OpenSections.pullback_comp` states, for every pair of bounded maps
`φ : A → B`, `ψ : B → C`, every ordinary open `U` and every concrete section `s`,

```
(ψ ∘ φ)* s = ψ* (φ* s),
```

where the intermediate open is `fφ⁻¹(U)` and the common target is the inverse
image of `U` under the composite spectrum map.

The private `transported_comp` lemma is an equality of actual elements of a
rational quotient. Its inputs are a source chart `d`, an intermediate chart
`b` with an actual restriction to the coefficient pullback of `d`, and a target
chart `w` with actual restrictions to the relevant intermediate and composite
pullbacks. Naturality of quotient transport first moves the intermediate
restriction through `ψ`. Uniqueness of chart arrows over the base identifies
the two restriction paths. The already proved
`pullbackCompIso_hom_transport` then identifies successive coefficient
transport with direct transport.

For each target chart `e`, the private `compositionRefinement` constructs a
finite rational refinement labeled by pairs `(d,b)`. Here `d` is a rational
chart contained in `U`, and `b` is a rational chart contained in the inverse
image of the interior of `d`. Each refinement component lies in the inverse
image under `fψ` of the interior of its selected `b`. The cover exists by
applying the constructed rational neighborhood theorem successively at the
source and intermediate points, then the finite relative-open refinement
construction of [RationalChartOpenRefinement](RationalChartOpenRefinement.md).

The proof constructs the required bounded restriction arrows from these locus
inclusions. The arbitrary-subchart formula for the original section pullback
identifies both direct and successive pullbacks on each refinement component.
`transported_comp` identifies their quotient elements there.
`Domain.FiniteCover.algebra_ext_of_restrict_eq` then identifies their elements
in the original target quotient. Extensionality of compatible families proves
the asserted section equality. Thus the comparison uses finite algebra
separation, rather than a test only on spectral values.

## Sheaf and locally ringed-space laws

`openSpectrumMap_comp` identifies the underlying continuous maps. This
topological equation does not use completeness.
`openAlgebraPresheafMap_comp` states the corresponding composition law for the
actual presheaf morphisms into pushforward presheaves. Its components are the
section equation above.

`algebraSheafedSpaceMap_id` and `algebraSheafedSpaceMap_comp` identify the actual
maps as morphisms of algebra-sheafed spaces. The latter law has the direction

```
algebraSheafedSpaceMap (ψ ∘ φ)
  = algebraSheafedSpaceMap ψ ≫ algebraSheafedSpaceMap φ.
```

The proofs use equality of the underlying continuous maps and extensionality
of the natural transformations on all ordinary opens. Applying the
scalar-forgetting functor on presheafed spaces gives
`ringSheafedSpaceMap_id` and `ringSheafedSpaceMap_comp`.
`locallyRingedSpaceMap_id` and `locallyRingedSpaceMap_comp` follow by
extensionality of morphisms of locally ringed spaces: their data are these
same actual ringed-space maps, and their locality proofs were already
constructed in RationalOpenMorphism.

## The functor and its scope

`locallyRingedSpaceFunctor K` has source
`PresentedAffinoidSpace K = (PresentedAffinoidAlgebra K)ᵒᵖ` and target
Mathlib's category `AlgebraicGeometry.LocallyRingedSpace`. It sends a
presentation to its actual Banach spectrum equipped with the concrete
ordinary-open structure sheaf and proved local stalk rings. On an opposite
arrow it uses `locallyRingedSpaceMap` of the original bounded algebra map.
The preceding identity and composition laws supply its functor laws.

`locallyRingedSpaceFunctor_forget` identifies its composite with the
forgetful functor to `TopCat` with the original
`Langlands.Analytic.affinoidSpectrumFunctor K`. This is an equality of
functors, with the same actual continuous spectral maps.

This is an internal construction and proof unit. Its provenance is the
concrete pullback and local-morphism constructions in RationalOpenPullback
and RationalOpenMorphism, the actual chart-comparison equations of
[RationalChartPullbackCoherence](RationalChartPullbackCoherence.md), and the
finite-domain algebra separation theorem of
[DomainAlgebraGluing](DomainAlgebraGluing.md). It introduces no further
original-literature assertion or assumed analytic output object.
It does not construct the comparison with the separately stored rational
sheaf, unrestricted analytic atlases, analytic etale or quasi-etale sites,
equivariant sites, or the Harris tower. Those remain further construction
obligations.
