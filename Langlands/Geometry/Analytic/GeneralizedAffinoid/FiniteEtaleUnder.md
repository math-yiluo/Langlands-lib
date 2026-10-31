# Algebraically finite étale positive-polyradius quotients under a base

Authors: Worker 56 and Worker 36. This adapts Worker 36's published strict
`FiniteEtaleUnder` construction to the actual arbitrary positive-polyradius
quotients and adds the relative spectrum functor.

Fix an ultrametric normed field `K` and an actual
`P : PresentedAffinoidAlgebra K`. Each presentation is a quotient of a finite
positive-polyradius restricted-series algebra by its specified closed ideal,
with the constructed quotient norm. Its arrows are all bounded `K`-algebra
maps. The definitions below impose no coefficient completeness or nontrivial
valuation, and retain zero arity, unit ideals, zero quotients, and empty
spectra.

## The full relative category

`algebraicallyFiniteEtaleUnderProperty P` selects the objects of the actual
Mathlib category `Under P` whose structural map is
`BoundedAlgHom.AlgebraicallyFiniteEtale`. This published predicate means that
the underlying ring map is both finite and étale. Its full subcategory is
`AlgebraicallyFiniteEtaleUnder P`, in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra`.

`mk` bundles such a specified bounded structural map. `baseMap` recovers that
map, and `homMap` recovers the bounded map in each relative arrow. `homMk`
admits every bounded map whose triangle commutes, and `homMap_homMk` verifies
that the map is retained exactly. `homMap_comp_baseMap` is the actual
triangle equation. Equality of the bounded maps determines equality of
relative arrows by `hom_ext`, using undercategory and full-subcategory
extensionality.

Every relative arrow is itself algebraically finite étale, as proved by
`homMap_algebraicallyFiniteEtale`. Apply the published generic cancellation
lemma `BoundedAlgHom.AlgebraicallyFiniteEtale.of_comp` to the source
structural map. The triangle rewrites the composite as the target
structural map. The generic lemma obtains ring-map finiteness by
`RingHom.Finite.of_comp_finite` and étaleness by
`Algebra.Etale.of_restrictScalars`. No finite-étale property is required as
additional arrow data.

`base P` is the identity structural map, so the category has an object over
every presentation. `inclusion P` into `Under P` is full and faithful.
`forget P` retains the actual target algebra and is faithful. The category
and functor laws come from the bounded-map category, undercategory, and full
subcategory; no category with assumed analytic properties is introduced.

## Algebraic triangles and boundedness

If `K` is complete and nontrivially normed, `algebraicHomEquiv X Y` is a
bijection from all algebraic `K`-algebra maps between the two target
quotients commuting with the structural maps to their relative hom-set.
No bound or continuity of the algebraic map is an input.

The published generalized `Banach` construction gives completeness of the
base and source quotient norms. The proof then applies the generic
`BoundedAlgHom.finiteTriangleEquiv`, whose finite Banach-module argument
constructs a norm bound from finiteness of the source structural map.
The relative-arrow constructors give the second bijection. The inverse
forgets the bound, and the inverse laws follow by reflexivity and arrow
extensionality. `algebraicHomEquiv_apply_toAlgHom` identifies the resulting
algebraic map with the original one.

Only this algebraic-hom comparison requires completeness and nontrivial
valuation. No such hypotheses are added to the category, cancellation, or
spectrum constructions.

## Actual spectra over the base

`spectrumFunctor P` composes the opposite of `forget P` with the published
`affinoidSpectrumFunctor K`. Its objects are the actual bounded
multiplicative spectra with their evaluation topologies, and its arrows
are continuous seminorm pullbacks. These normed-algebra spectra are
constructed even without coefficient completeness.
`spectrumFunctor_map_apply` gives the arrow formula
`x ↦ (a ↦ x (homMap h.unop a))`.

`spectrumOverFunctor P` retains each geometric structural map. The opposite
inclusion takes values in `(Under P)ᵒᵖ`; Mathlib's
`Over.opEquivOpUnder P` reverses the arrows to give objects over
`Opposite.op P`; `Over.post (affinoidSpectrumFunctor K)` then applies the
actual spectrum functor. Its target is
`Over (TopCat.of (BanachSpectrum P))`.

`spectrumOverFunctor_obj_apply` states that the structural map sends `x` to
`a ↦ x (Y.baseMap a)`. `spectrumOverFunctor_map_apply` states that each
relative arrow is pullback by its retained bounded map. Both are
definitional formulas. The relative triangles and functor laws follow
from the categorical constructions. `spectrumOverFunctor_forget` proves
by reflexivity that forgetting the structural spectrum maps recovers
`spectrumFunctor P` exactly.

## Original sources and derived scope

Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
Definition 3.3.1(i), printed/PDF p. 17, defines a finite morphism of
affinoid spaces through a finite Banach algebra. Definition 3.3.9(i),
printed/PDF p. 19, requires algebraic finite étaleness on every affinoid
domain for a finite étale analytic morphism. These passages were read
directly in the registered original
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.

The exact relative category, algebraic-hom comparison, and relative
spectrum functor are internal derived infrastructure. They reuse the
published generic finite-étale cancellation, automatic boundedness,
actual generalized quotient and Banach constructions, and Mathlib's
undercategories and opposite/postcomposition functors. They are not
separately numbered results attributed to the lectures.

The construction concerns the underlying algebraic finite-étale
condition on these specified bounded maps. It does not prove the
source's all-domain analytic condition, analytic étaleness of the
spectrum maps, tensor representability, arbitrary analytic base change,
analytic atlases, coverings, or an étale or quasi-étale site. Over
incomplete `K` the quotient and spectrum constructions retain their
normed-algebra meaning; no identification with complete affinoid
analytic spaces is asserted.
