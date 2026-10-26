# Algebraically finite étale affinoid objects under a continuous action

Author: Worker 36.

Fix an ultrametric normed field `K`, a group `G` with a topology, and an
actual object `X : NormContinuousAffinoidAction K G`. This derived
construction forms the category of equivariant bounded maps out of `X`
that are algebraically finite étale on the underlying presented strict
affinoid algebras. It retains every equivariant bounded arrow commuting
with the displayed base maps. For a topological group, its opposite has
a functor to continuous topological group actions over the actual
bounded multiplicative spectrum of `X`.

The underlying algebras remain the existing finite Tate quotients by
closed ideals with their quotient norms. The action on each quotient
has continuous forward element orbits in that norm, as required by the
published `NormContinuousAffinoidAction` construction. When `K` is
complete these algebras are complete. The present local construction
adds no completeness assumption; it also retains trivial valuations,
zero quotients, zero presentation arity, and empty spectra. The field
and group lie in independent universes.

## The actual relative category

`algebraicallyFiniteEtaleActionUnderProperty X` is the property on
Mathlib's `Under X` that its displayed equivariant bounded structural
map is algebraically finite étale. This means exactly the existing
`BoundedAlgHom.AlgebraicallyFiniteEtale` predicate, requiring finiteness
and étaleness of the underlying ring map. Its full subcategory is
`AlgebraicallyFiniteEtaleAffinoidActionUnder X`. The category and its
laws are inherited from the actual action category, undercategory, and
full subcategory.

`mk` constructs an object from an equivariant arrow and the algebraic
property of its actual bounded map. `baseHom` retains that equivariant
arrow, and `baseMap` retains its bounded algebra map. For a morphism,
`homAction` and `homMap` recover the equivariant arrow and bounded map,
respectively. `homMk` admits every compatible equivariant triangle.
`boundedHomMk` starts directly with a bounded map, its equivariance
equations, and its bounded algebra triangle; equality of the retained
bounded maps proves equality of the corresponding equivariant arrows.
The two constructor evaluation lemmas verify that no map is changed.

`baseHom_comp_homAction` and `homMap_comp_baseMap` give the triangle
equations. The latter follows by applying the action category's bounded
map accessor to the former. `hom_ext` proves that equality of the
bounded maps determines the arrows: it uses extensionality successively
in the action category, undercategory, and full subcategory.

Every arrow is itself algebraically finite étale, as proved by
`homMap_algebraicallyFiniteEtale`. Its proof applies the published
finite-étale cancellation lemma to the source structural map. The
triangle rewrites the composite as the target structural map, which
is finite étale by the target's object property. Thus finite étaleness
of a morphism is derived rather than required as additional arrow data.

`base X` is the identity structural map, available over every action.
`inclusion X` into `Under X` is full and faithful. `forget X` retains
the target action and is faithful. `forgetAction X` has values in the
published `AlgebraicallyFiniteEtaleAffinoidUnder X.obj.V`: it retains
the actual bounded structural maps and the actual bounded arrows, as
the two comparison evaluation lemmas state. It is faithful because an
equivariant relative arrow is determined by its bounded map. No
fullness or essential surjectivity of this last functor is asserted.

## Continuous equivariant spectra over the base

Assume now that `G` is a topological group. `spectrumFunctor X` composes
the opposite of `forget X` with the published inverse-pullback spectrum
functor. Its objects are the actual bounded multiplicative spectra with
their continuous `G` actions, and its arrows are continuous equivariant
seminorm-pullback maps.

`spectrumOverFunctor X` retains the geometric structural maps as well.
It first includes the opposite relative category in `(Under X)ᵒᵖ`.
Mathlib's `Over.opEquivOpUnder X` reverses the structural arrows,
giving objects over `Opposite.op X`. Finally `Over.post` applies the
published continuous equivariant spectrum functor to those objects and
triangles. Its target is
`Over (NormContinuousAffinoidAction.spectrum X)` in the category
`ContAction TopCat G`. All relative triangle and functor laws come from
these categorical constructions; no desired geometric maps or
continuity proofs are supplied as assumptions.

`spectrumOverFunctor_obj_apply` identifies the structural map on
seminorms: it sends `x` to the seminorm `a ↦ x (Y.baseMap a)`.
`spectrumOverFunctor_map_apply` identifies each arrow by the same
pullback formula for its actual bounded map. Both formulas hold by
reflexivity. `spectrumOverFunctor_forget` proves by reflexivity that
forgetting the geometric base recovers `spectrumFunctor X` exactly.
The existing spectrum functor supplies equivariance and joint
continuity from continuous algebra-element orbits, rather than from
new hypotheses on the spectrum.

As in `NormContinuousAction`, the Lean file installs
`NormContinuousAffinoidAction.topCatSelfForget` locally. A downstream
file spelling these continuous-action targets explicitly can install
that same identity forgetful instance locally.

## Sources, provenance, and remaining obligations

Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
Definition 3.3.1(i), printed/PDF p. 17, describes finite affinoid
morphisms through finite Banach algebras. Definition 3.3.9(i), p. 19,
requires algebraic finite étaleness on every affinoid domain for an
analytic finite étale morphism. This file constructs only the relative
algebraic prerequisite over the specified presented affinoids. It does
not prove that all-domain condition or assert analytic étaleness of its
spectrum maps. Registered literature:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Étale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, printed/PDF pp. 1–3, motivates
continuous analytic actions and equivariant arrows. Section 1.2, p. 3,
uses equivariant étale or quasi-étale objects over a fixed base to
define the corresponding sites. The present norm-orbit category is a
restricted, fixed-field local prerequisite. It neither identifies its
continuity condition with the full analytic automorphism topology nor
constructs the manuscript's analytic `G-An`, étale or quasi-étale
sites, coverings, or their base-change stability. Tensor
representability and analytic atlases remain separate obligations.
Registered literature:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

This exact full-subcategory construction, its faithful comparison, and
its relative spectrum functor are internal derived infrastructure, not
numbered results attributed to those sources. They reuse the published
`FiniteEtaleUnder` cancellation and relative category and the published
`NormContinuousAction` category and continuous spectrum construction.
Mathlib's undercategories, full subcategories, opposite equivalence,
and postcomposition functor supply the categorical laws.
