# Homology of a diagram of complexes

Author: Worker 13.

This module constructs a natural isomorphism between taking homology
objectwise in a diagram of complexes and taking homology in the category
of diagrams. It retains every diagram transition and is natural in
chain maps. It is reusable infrastructure for the varying-cover
associated sheaf complexes of the Harris framework.

## Provenance and inputs

This is an internal categorical construction from Mathlib, pinned at
`5ed2965256430c3649e86755f9576b54eca72435`. Its inputs are an arbitrary
category `J : Type uJ` with morphisms in universe `vJ`, an abelian category
`C : Type uC` with morphisms in universe `vC`, a degree type
`ι : Type uι`, an arbitrary complex shape `c : ComplexShape ι`, and a
degree `q : ι`. These five universes are independent. No topology,
finiteness, filteredness, coefficient ring or space is required.

Mathlib's `Algebra/Homology/Functor.lean` supplies
`HomologicalComplex.complexOfFunctorsToFunctorToComplex`, which sends
a complex of diagrams `K` to the diagram of complexes `K.asFunctor`.
Its evaluation at `j` has terms `(K.X n).obj j`, differentials
`(K.d p q).app j`, and transition chain maps with degree component
`(K.X n).map a`. The same import supplies the pointwise abelian
structure on `J ⥤ C`.

Exact evaluation gives the canonical comparison
`(K.sc q).mapHomologyIso ((evaluation J C).obj j)`, from homology of
the evaluated short complex to evaluation of its homology.
Mathlib's `Algebra/Homology/ShortComplex/PreservesHomology.lean`
supplies this isomorphism, its naturality in short-complex maps, and
`NatTrans.app_homology`, which expresses its compatibility with
natural transformations between exact functors. No new external
mathematical assertion is attributed to Harris or Berkovich.

## Constructed isomorphism

Write `Hq_C = HomologicalComplex.homologyFunctor C c q` and
`T = HomologicalComplex.complexOfFunctorsToFunctorToComplex`.
The definition `diagramHomologyIso c q` has type

```text
T ⋙ (Functor.whiskeringRight J (HomologicalComplex C c) C).obj Hq_C
  ≅ HomologicalComplex.homologyFunctor (J ⥤ C) c q.
```

At a complex `K`, its source is the diagram whose value at `j` is
`Hq_C(K.asFunctor.obj j)` and whose map at `a : i ⟶ j` is
`Hq_C(K.asFunctor.map a)`. Its target is the actual categorical
homology `K.homology q` in `J ⥤ C`.

The isomorphism at `K` and `j` is exactly the canonical
`mapHomologyIso` for evaluation. This formula is exposed by
`diagramHomologyIso_hom_app`.

For a diagram arrow `a : i ⟶ j`, the theorem
`diagramHomologyIso_transition` states

```text
Hq_C(K.asFunctor.map a) ≫ e_K,j
  = e_K,i ≫ (K.homology q).map a.
```

For a chain map `f : K ⟶ L`, the theorem
`diagramHomologyIso_naturality` states, at each `j`,

```text
Hq_C((T.map f).app j) ≫ e_L,j
  = e_K,j ≫ (HomologicalComplex.homologyMap f q).app j.
```

Both equations have reassociated variants. Thus the definition
assembles the individual evaluation isomorphisms into an isomorphism
of full diagrams, itself natural in the input complex.

## Implemented proof

The construction uses `NatIso.ofComponents` twice. The inner
construction packages the canonical isomorphisms for evaluation.
For an index arrow `a`, apply `NatTrans.app_homology` to
`(evaluation J C).map a` and the short complex `K.sc q`.
Composing that equation with the evaluation comparison cancels its
inverse and proves transition naturality.

For the outer construction, equality of natural transformations is
checked at every `j`. At that component,
`ShortComplex.mapHomologyIso_hom_naturality` applied to the short
complex map induced by `f` proves the required equality. The component
formula is definitional, and the two exposed equations are the two
levels of naturality of the constructed isomorphism.

## Scope

This is ordinary categorical homology. It makes no assertion that
homology commutes with any infinite limit or colimit and constructs
no derived functor, global sections, compact support, Shimura scheme,
level tower or group action. The intended application evaluates
actual associated sheaf complexes at varying covers; identifying
those geometric inputs and their cohomology remains separate work.
