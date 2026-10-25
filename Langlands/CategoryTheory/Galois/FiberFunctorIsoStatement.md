# Natural isomorphisms between fibre functors

`Langlands.CategoryTheory.Galois.FiberFunctorIsoExists` states that two fibre
functors on a Galois category admit a natural isomorphism. Its complete parameters
are independent universes `v u`, a category `C : Type v` with
`Category.{u} C` and `GaloisCategory C`, functors
`F G : C ⥤ FintypeCat.{u}`, and instances
`PreGaloisCategory.FiberFunctor F` and `PreGaloisCategory.FiberFunctor G`.
Its body is exactly `Nonempty (F ≅ G)`.

Here `F ≅ G` is an isomorphism in the functor category: it includes natural
transformations in both directions and their inverse identities. Thus the
conclusion requires compatible bijections on every object, not merely equality
of fibre cardinalities. `Nonempty` asserts existence without selecting an
isomorphism or asserting uniqueness. The finite-set value universe equals the
Hom universe `u`; the object universe `v` remains independent.

## Source and axiom comparison

The original source is A. Grothendieck et al., *Revêtements étales et groupe
fondamental (SGA 1)*, recomposed annotated edition, arXiv:math/0206203v2,
Exposé V, Corollary 5.7, printed p.107 / PDF p.123. That corollary states that
fundamental fibre functors on a Galois category are isomorphic. The following
paragraph describes their category as a connected groupoid. The present
statement records the existence part for two specified functors; it does not
state the accompanying result about fundamental pro-objects or that every
natural transformation is invertible.

SGA 1, Exposé V, §4, printed p.98 / PDF p.114 lists axioms (G1)–(G6).
Definition 5.1, printed p.104 / PDF p.120 characterizes a Galois category by
these axioms and calls a functor satisfying (G4)–(G6) fundamental, with a
footnote recommending the term fibre functor.

The Lean hypotheses use the existing classes in
`Mathlib.CategoryTheory.Galois.Basic`. `PreGaloisCategory` provides a terminal
object, pullbacks, finite coproducts, finite-group quotients, and the condition
that every monomorphism identifies its domain with a direct summand.
`FiberFunctor` requires preservation of terminal objects, pullbacks, finite
coproducts, epimorphisms and finite-group quotients, together with reflection
of isomorphisms. `GaloisCategory` extends `PreGaloisCategory` by existence of
a fibre functor valued in `FintypeCat` in the Hom universe.

This is Mathlib's axiom interface for the source, rather than a literal
transcription of all six original axioms. In particular, SGA 1's (G3) includes
a strict-epimorphism/monomorphism factorization for every morphism; Mathlib
omits that factorization axiom and retains the direct-summand condition for
monomorphisms. Mathlib's module documentation explains that the omitted
factorization follows from the fundamental theorem of Galois categories.
Its fibre-functor class asks for preservation of all epimorphisms, whereas the
original (G5) mentions strict epimorphisms. These interface choices are explicit
in the hypotheses above. No isomorphism between the two functors, chosen
pro-object points, or comparison natural transformation is an input.

## Scope and status

This module defines a proposition and supplies no proof. It is a general
categorical statement; geometric finite étale categories and their
fibre-functor axioms require separate results before applying it.

The retained source is registered as `sga1-arxiv-math-0206203v2`, with SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
