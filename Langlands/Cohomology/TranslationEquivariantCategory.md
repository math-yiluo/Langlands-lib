# Morphisms of translation-equivariant objects

This internal construction equips the existing
`Langlands.Cohomology.TranslationAction.Equivariant` objects with their actual
morphism category. It uses the published `TranslationAction.Data` and does not
introduce a new notion of equivariant object.

Let `C : Type u` and `D : Type u'` be categories with morphisms in universes `v`
and `v'`. Let `G : Type w` be a monoid, `Γ : C ⥤ D`, and `T g : C ⥤ C` for
each `g : G`, with fixed data `𝒯 : TranslationAction.Data Γ T`. An existing
equivariant object `F` has an underlying object `F.obj` and structure maps
`F.act g : (T g).obj F.obj ⟶ F.obj`, with the unit and product laws recorded
in that data. This file requires neither abelian categories nor exactness,
additivity, or preservation of injectives.

A morphism `f : F ⟶ E` is an underlying morphism `f.hom : F.obj ⟶ E.obj`
such that, for every `g`,

```text
F.act g ≫ f.hom = (T g).map f.hom ≫ E.act g.
```

`Hom.id` and `Hom.comp` use the underlying identity and composition. The
identity commutation law follows from preservation of identities by `T g`.
The composition law follows by applying the two commutation equations and
preservation of composition. Extensionality in the underlying morphism
reduces the category laws to those of `C`. `id_hom` and `comp_hom` give the
definitional underlying-map formulas.

`forget : Equivariant 𝒯 ⥤ C` takes the underlying object and morphism.
It is faithful because morphisms are determined by their underlying maps.
No fullness assertion is made.

`mkIso e comm` lifts an underlying isomorphism `e : F.obj ≅ E.obj` whose
forward map commutes with the actions. The inverse commutation equation is
proved by cancellation with `e.hom`, the given commutation equation, and the
functorial image of `e.inv ≫ e.hom = 𝟙 _`. The two inverse laws reduce to
the underlying inverse laws. Its underlying forward and inverse maps are
definitionally `e.hom` and `e.inv`, as recorded by the two final lemmas.

This is categorical infrastructure derived from the existing project
definitions and the ordinary category and functor laws in Mathlib. There is
no new original-literature theorem. The file does not construct limits,
abelian structure, injective resolutions in this category, or cohomology
functoriality. Those require further constructions. It adds no topology or
smoothness conditions and does not instantiate a Harris level space.
