# Group restriction of relative finite étale positive-polyradius actions

Authors: Worker 56 and Worker 36.

This derived construction adapts the published strict
`EquivariantFiniteEtaleRestriction` implementation to actual arbitrary
positive-polyradius quotient actions. It restricts the acting group of
every algebraically finite-étale object under a fixed continuous-orbit
action, retaining the bounded structural maps and all relative arrows.
For topological groups, it constructs a natural comparison of the
continuous spectra over the restricted base.

## Relative restriction

Let `K` be an ultrametric normed field, let `G` and `H` be groups with
topologies, and let `f : H →ₜ* G` be a continuous group homomorphism.
The field and both groups have independent universes. Continuity of
group operations is required only in the spectrum section below.
Fix `X : PresentedAffinoidAlgebra.NormContinuousAction K G`.

`AlgebraicallyFiniteEtaleActionUnder.restrict f X` includes the full
finite-étale undercategory in `Under X` and applies `Under.post` to
`NormContinuousAction.restrict f`. This retains the actual quotient
algebra and bounded structural map of every object while precomposing
its action with `f`. The structural map's finite and étale ring-map
properties are unchanged, so its existing proof places the result in
the finite-étale undercategory of the restricted base.

The underlying presentation is the actual closed-ideal quotient of a
finite positive-polyradius restricted-series algebra. Every bounded
equivariant commuting triangle is retained in the source relative
category. Its image under restriction is the same bounded triangle,
now equivariant for `H`.

`restrict_obj_baseMap` and `restrict_map_homMap` identify the restricted
structural and arrow maps with the original bounded maps by reflexivity.
The restriction functor is faithful: applying the bounded-map accessor
to equality of image arrows, followed by relative extensionality,
recovers equality of the original arrows. Fullness is not asserted.

`restrict_forget` says that forgetting the relative base commutes exactly
with group restriction. `restrict_forgetAction` says that forgetting all
action data erases group restriction exactly, leaving the same object
and arrows in `AlgebraicallyFiniteEtaleUnder X.obj.V`. Both equalities
of functors are reflexive.

## Continuous spectra over the base

Assume additionally that `G` and `H` are topological groups.
The imported `NormContinuousAction.spectrumRestrictIso f X` is an
isomorphism from the spectrum of the restricted algebra action to
restriction of the original spectrum action. Both directions are the
identity on bounded multiplicative seminorms. Its equivariance is
proved using `f (h⁻¹) = (f h)⁻¹` in the inverse-pullback action.
Continuity uses the actual evaluation topology and the already
constructed continuous spectrum functors.

`AlgebraicallyFiniteEtaleActionUnder.spectrumRestrictionIso f X`
has source functor

```text
(restrict f X).op
  ⋙ spectrumOverFunctor ((NormContinuousAction.restrict f).obj X)
  ⋙ Over.map (NormContinuousAction.spectrumRestrictIso f X).hom
```

and target functor

```text
spectrumOverFunctor X ⋙ Over.post (ContAction.res TopCat f).
```

Both functors land over the same continuous `H`-action, namely
restriction of the original base spectrum. `Over.map` uses the base
comparison in the displayed direction: it postcomposes structural
arrows from the spectrum of the restricted base to that common base.
`Over.post` restricts the entire original structural arrow.

At each relative object, `Over.isoMk` uses the imported identity
spectrum comparison on its target quotient. The commuting triangle
reduces to equality of pullbacks along the same structural bounded
map. Naturality similarly reduces to equality of pullbacks along each
relative bounded map. The implemented proofs use overcategory,
full-subcategory, action, and topological-map extensionality, with
pointwise reflexivity. The forward and inverse evaluation lemmas
identify both comparison maps with the identity on seminorms.

The spectrum section installs the shared local identity forgetful
instance
`Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget`.
Thus `ContAction TopCat` refers to the actual spectrum topology.

## Sources, provenance, and scope

Berkovich's unfinished *Étale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, printed/PDF pp. 1–3, defines continuous
analytic actions and morphisms changing groups along a continuous
homomorphism from the source acting group to the target acting group.
Section 1.2, p. 3, introduces the relative equivariant étale and
quasi-étale categories and their sites. These motivate the fixed-field
local restriction constructed here. Registered literature:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The exact relative functor and spectrum comparison are internal
derived infrastructure adapting Worker 36's strict construction.
They reuse the actual generalized quotient action and finite-étale
undercategories, their spectrum-over-base functors, the generalized
spectrum-restriction comparison, and Mathlib undercategory and
overcategory operations. They do not assume an output algebra, a
comparison isomorphism, or a desired continuity theorem.

No injectivity or surjectivity of `f`, coefficient completeness,
nontrivial valuation, common operator bound, reducedness, or nonempty
spectrum is assumed. Zero quotients and empty spectra remain allowed.
For incomplete `K`, the objects retain their normed-quotient meaning;
the manuscript works over complete nonarchimedean fields. This
construction retains `K` and does not identify norm-orbit continuity
with the manuscript's analytic automorphism topology. It does not
establish analytic étaleness on every affinoid domain, tensor
representability, analytic base change, atlases, coverings, or
equivariant analytic sites.
