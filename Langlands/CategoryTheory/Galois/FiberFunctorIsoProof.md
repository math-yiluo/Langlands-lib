# Isomorphisms between fibre functors

`Langlands.CategoryTheory.Galois.fiberFunctorIsoExists` proves the published
proposition `Langlands.CategoryTheory.Galois.FiberFunctorIsoExists F G`.
The signature retains independent universes `v u`, a category `C : Type v`
with `Category.{u} C` and `GaloisCategory C`, functors
`F G : C ⥤ FintypeCat.{u}`, and both
`PreGaloisCategory.FiberFunctor` instances. The conclusion is
`Nonempty (F ≅ G)`, an actual isomorphism in the functor category.

## Implemented proof

The private helper first proves `Nonempty (F ⟶ G)`. Let `P` be Mathlib's category
`PointedGaloisObject F`, and restrict `G`, followed by the inclusion into types,
along `PointedGaloisObject.incl F`. This gives a functor
`H : P ⥤ Type u`. Mathlib's instance makes `P` cofiltered or empty.
For every object `A` of `P`, `H.obj A` is finite because it is a fibre of `G`.
It is nonempty by `nonempty_fiber_of_isConnected G A.obj`, since a Galois object
is connected.

The theorem `nonempty_sections_of_finite_cofiltered_system H` now gives points
`s A : G.obj A.obj` satisfying `G.map f.val (s A) = s B` for every pointed
morphism `f : A ⟶ B`. This is where the required coherence is proved to exist;
no coherent family is a hypothesis.

These points define a cocone on
`(PointedGaloisObject.incl F).op ⋙ coyoneda` with vertex
`G ⋙ FintypeCat.incl`. Its component at `A` sends a morphism
`h : A.obj ⟶ X` to `G.map h (s A)`. Functoriality of `G` proves naturality
in `X`; the section equation proves compatibility with every pointed morphism.
The colimit universal property `PointedGaloisObject.isColimit F` then produces
a natural transformation
`F ⋙ FintypeCat.incl ⟶ G ⋙ FintypeCat.incl`.
The fully faithful right-whiskering functor induced by `FintypeCat.incl`
lifts it to `F ⟶ G`.

Apply this helper in both directions to obtain `f : F ⟶ G` and `g : G ⟶ F`.
Mathlib's `FibreFunctor.end_isIso` makes both `f ≫ g` and `g ≫ f`
isomorphisms. The first makes `f` a monomorphism. The morphism
`inv (g ≫ f) ≫ g` is a section of `f`, since its composite with `f` equals
the identity on `G`. Thus `f` is also a split epimorphism, and
`isIso_of_mono_of_isSplitEpi f` gives the required natural isomorphism
`asIso f`.

## Provenance and scope

The target is A. Grothendieck et al., *Revêtements étales et groupe fondamental
(SGA 1)*, recomposed annotated edition, arXiv:math/0206203v2, Exposé V,
Corollary 5.7, printed p.107 / PDF p.123. It states that fundamental fibre
functors on a Galois category are isomorphic. The registered source is
`sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
The axiom comparison is documented in the imported statement's Markdown.

The implemented proof uses Mathlib's
`Mathlib.CategoryTheory.Galois.Prorepresentability` and
`Mathlib.CategoryTheory.CofilteredSystem`, following the route proposed by
Worker 360. The helper and cocone argument are derived constructions for this
proof. This is not a transcription of SGA 1's proof through its earlier
propositions.

The finite-system existence theorem allows independent object, morphism and
value universes. The colimit presentation uses values in the morphism universe
`u`, exactly as in the target. No relation between `v` and `u` is imposed.
This proof establishes existence only; it makes no uniqueness assertion and
does not prove geometric finite étale Galois-category axioms.
