# Functorial cohomology of compatible coefficient diagrams

This module equips the compatible coefficient diagrams of
`EtaleCohomologyDiagram` with their actual morphism category. It constructs
cohomology as a functor in these coefficients and identifies degree-zero
cohomology naturally with ordinary global sections.

Fix a commutative ring `R : Type u`, a category `J : Type v` with morphisms
in universe `w`, and a functor `S : J ⥤ Scheme.{u}ᵒᵖ`. For every arrow
`a : i ⟶ j`, assume the scheme morphism
`f_a := (S.map a).unop : X_j ⟶ X_i` is étale, where
`X_i := (S.obj i).unop`. Coefficients remain in `ModuleCat.{u} R`.
All definitions are in
`Langlands.Geometry.EtalePullback.CoefficientDiagram`.

## The category of compatible coefficients

An object is the imported `CoefficientDiagram R S`: it consists of actual
small-étale module sheaves `D.obj i` on the schemes `X_i`, with morphisms
`D.map a : f_a* (D.obj i) ⟶ D.obj j` satisfying the identity and composition
laws of that construction. Here `f_a*` denotes its restriction functor;
none of these coefficient morphisms is required to be invertible.

`Hom D E` consists of sheaf morphisms `α.app i : D.obj i ⟶ E.obj i`
satisfying, for every arrow `a : i ⟶ j`,

```text
D.map a ≫ α.app j = (diagramRestriction R S a).map (α.app i) ≫ E.map a.
```

`Hom.id` and `Hom.comp` use the identity and composition of sheaf maps at
each vertex. Compatibility of composition follows by applying the two
compatibility equations and functoriality of restriction. These operations
define the `Category (CoefficientDiagram R S)` instance. Its laws are proved
by extensionality in the components and the corresponding sheaf-category
laws. `id_app` and `comp_app` give the component formulas. `evaluation i`
is the functor to the actual sheaf category on `X_i` obtained by evaluating
objects and morphisms at `i`.

## Functorial cohomology

For `q : ℕ`, the imported `D.cohomology q` is the diagram whose object at
`i` is the right-derived global-section module `H^q(X_i, D.obj i)`. Its
map on `a` is pullback along `f_a` followed by cohomology of `D.map a`.

`cohomologyMap α q` is a natural transformation from `D.cohomology q` to
`E.cohomology q`. Its component at `i` is exactly

```text
(EtaleDerivedSections.cohomology X_i R q).map (α.app i).
```

Its naturality proof combines the defining compatibility of `α` with the
published naturality of derived pullback in the coefficient sheaf. The
identity and composition laws hold componentwise by functoriality of
right-derived sections. This gives the actual functor

```text
cohomologyFunctor q : CoefficientDiagram R S ⥤ (J ⥤ ModuleCat.{u} R).
```

No cohomology maps or cohomology compatibility laws are part of the input
morphism data.

## Ordinary sections and the degree-zero comparison

`sections D` has object `Γ(X_i, D.obj i)` at `i`, using the imported
ordinary global-section functor. Its arrows are constructed by transporting
the arrows of `D.cohomology 0` through the canonical component isomorphisms
`EtaleDerivedSections.cohomologyZeroIso`. In formulas, writing
`e_i : H⁰(X_i, D.obj i) ≅ Γ(X_i, D.obj i)`, its map on `a` is

```text
e_i.inv ≫ (D.cohomology 0).map a ≫ e_j.hom.
```

Cancellation of these isomorphisms proves the functor laws.
`sections_map` proves that this transported arrow is the ordinary map

```text
(sectionsMap f_a R).app (D.obj i) ≫
  (EtaleDerivedSections.sections X_j R).map (D.map a).
```

Thus the transition is actual restriction of sections followed by the
coefficient-sheaf morphism. The proof uses naturality of the degree-zero
comparison and `EtalePullback.cohomologyMap_zero`, and cancels the comparison
at the source. `cohomologyZeroIso D` packages the component isomorphisms
into a natural isomorphism `D.cohomology 0 ≅ D.sections` of `J`-diagrams.

`sectionsFunctor` acts on objects by `sections` and on coefficient morphisms
by conjugating `cohomologyFunctor 0` through these natural isomorphisms.
Its identity and composition laws again follow by cancellation.
`sectionsFunctor_map_app` proves that the resulting component at `i` is
exactly ordinary sections applied to `α.app i`; this is the naturality
identity for the imported degree-zero comparison. Finally,
`cohomologyZeroFunctorIso` is a natural isomorphism of functors

```text
cohomologyFunctor (R := R) (S := S) 0 ≅ sectionsFunctor.
```

The comparison is therefore natural both in arrows of the scheme diagram
and in compatible changes of the coefficient sheaves.

## Provenance and retained specialization

This is internal categorical infrastructure derived from
`EtaleCohomologyDiagram`, the published small-étale restriction and derived
pullback constructions, and the canonical degree-zero comparison for
right-derived global sections. It does not claim a new named result from
Harris or Berkovich. The proofs implement componentwise category laws,
naturality, and transport through the existing isomorphisms.

The scheme diagram is fixed while the coefficient diagram varies; the
scalar ring also stays fixed. The construction provides ordinary étale
cohomology and ordinary global sections. It does not construct compact
support, scalar change, derived inverse limits, a Shimura tower, or its
coefficient sheaves. Applying it to Harris still requires the actual scheme
tower, étaleness of its transitions, and compatible coefficient sheaf maps.
Those geometric constructions and the comparison with the separate
scheme-automorphism action remain explicit further obligations.
