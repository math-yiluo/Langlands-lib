# Algebraically finite étale affinoid algebras under a fixed base

Author: Worker 36.

This derived construction fixes an actual presented strict affinoid algebra
`P` and constructs a category of specified bounded algebraically finite étale
maps `P → Q`. Its arrows are all compatible bounded algebra maps between the
targets. The carrier of every target remains its existing finite Tate quotient
by a closed ideal, with its actual quotient norm.

The generic lemma `BoundedAlgHom.AlgebraicallyFiniteEtale.of_comp` proves
cancellation: if `f : A → B` and `g ∘ f : A → C` are algebraically finite
étale, then `g : B → C` is algebraically finite étale. Module finiteness of
`C` over `B` follows from that over `A`: the same finite generating family
works after enlarging scalars. The proof uses
`RingHom.Finite.of_comp_finite`. For étaleness, it installs the three algebra
structures induced by the actual ring maps and their compositional scalar
tower, then applies `Algebra.Etale.of_restrictScalars`. The maps' existing
boundedness is retained; this lemma needs no completeness, ultrametricity or
nontrivial valuation. Its coefficient and algebra types may lie in independent
universes.

`algebraicallyFiniteEtaleUnderProperty P` selects the objects of Mathlib's
`Under P` whose displayed structural map satisfies the existing predicate from
`FiniteEtaleAlgebra`. `AlgebraicallyFiniteEtaleAffinoidUnder P` is its full
subcategory. Thus neither the underlying algebras nor a category with prescribed
analytic properties is supplied as arbitrary data. The category laws are
inherited from the actual bounded-map category, undercategory and full
subcategory.

The constructors `mk` and `homMk` take an actual bounded structural map or
commuting triangle. The accessors `baseMap` and `homMap` recover those very
maps. `homMap_comp_baseMap` proves the triangle equation, and `hom_ext`
states that an arrow is determined by its bounded map. Applying cancellation
to that triangle proves `homMap_algebraicallyFiniteEtale`: every compatible
bounded arrow between two such objects is itself algebraically finite étale.
This property is derived, rather than imposed on morphisms as extra data.

The object `base P` uses the identity map. The inclusion into `Under P` is
full and faithful. The functor `forget P` forgets the structural map and is
faithful, and `toFiniteEtale P` factors it through the published wide category
of algebraically finite étale maps using the preceding cancellation result.
No completeness of the coefficient field is required for these constructions.

If the coefficient field is complete and nontrivially normed,
`algebraicHomEquiv X Y` identifies the actual hom-set with all algebraic
`K`-algebra maps between the targets that commute with the specified base
maps. It composes the published `BoundedAlgHom.finiteTriangleEquiv` with the
undercategory/full-subcategory constructors. That existing result constructs a
norm bound using the finite Banach-module theorem; no bound or continuity of
the algebraic arrow is assumed. The displayed evaluation lemma verifies that
the resulting arrow has precisely the original algebraic map. This comparison
requires a nontrivial valuation; the category and cancellation theorem also
allow trivial valuations. Zero quotients and empty presentations are allowed
throughout.

For a complete coefficient field, `spectrumFunctor P` applies the existing
actual spectrum functor to the opposite of the forgetful functor. The
evaluation formula verifies that a geometric arrow sends a seminorm `x` to
its pullback along the underlying bounded algebra map. This supplies actual
topological spaces and continuous maps in the geometric direction.

The source context is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Definition 3.3.1(i), printed/PDF p. 17, and Definition
3.3.9(i), printed/PDF p. 19. The former defines finite affinoid morphisms
using finite Banach algebras; the latter requires algebraic finite étaleness
on every affinoid domain. The present category isolates the algebraic
fixed-base prerequisite. It does not prove that all-domain requirement,
analytic base change, or an analytic étale site. Its spectrum functor does
not assert analytic étaleness of the resulting maps.

The registered original is `berkovich-2009-trieste-analytic-spaces`, retained
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
available at
https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
The fixed-base construction and cancellation proof are internal derived
infrastructure, rather than a verbatim theorem from those lectures. Their
algebraic ingredients are the pinned Mathlib results in
`RingTheory.Finiteness.Basic` and `RingTheory.Etale.Basic`; the categorical
ingredients are `CategoryTheory.Comma.Over.Basic` and
`CategoryTheory.ObjectProperty.FullSubcategory`. Automatic boundedness and
seminorm pullback reuse the already published analytic constructions by name.
