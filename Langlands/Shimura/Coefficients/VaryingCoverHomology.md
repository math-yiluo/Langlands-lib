# Coverwise homology of varying-cover associated complexes

Author: Worker 13.

The actual varying-cover associated complexes already have two
presentations: a complex of sheaf diagrams and a diagram of sheaf
complexes. This module identifies the diagram of homologies in the
second presentation with the associated coefficient homology diagram.
The isomorphism retains all actual cover-transition chain maps and is
natural in coefficient chain maps.

## Provenance and inputs

This is an internal categorical derivation from
`Langlands.Cohomology.DiagramHomology` and
`Langlands.Shimura.Coefficients.VaryingCoverExact`. The former assembles
canonical homology comparison isomorphisms for exact evaluations into
a natural isomorphism of whole diagrams. The latter supplies the
canonical homology isomorphism for exact varying-cover association.
`AssociatedComplex` supplies both actual complex presentations and
their degree, differential and map formulas. The already existing
`AssociatedPowerHomologyEvaluation` supplies the single-cover
evaluation isomorphism used to state the component factorization.
No inverse-limit result from that module is invoked.

The inputs are an actual scheme `X : Scheme.{u}`, a commutative ring
`R : Type u`, an index category `J : Type uJ` with morphisms in
universe `vJ`, a group diagram `D : J ⥤ GrpCat.{u}`, and
`Y : EquivariantDiagram D X.Etale`. There is an explicit hypothesis

```text
hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j).
```

At each cover this means a finite deck group, a finite surjective
structure morphism of the actual étale cover, and a unique deck
translation between geometric lifts over the same base point. It
provides the hypotheses of the proved geometric comparison used in
the actual transitions. No transition or comparison theorem is
assumed as additional input.

Scheme, ring, coefficient modules and group carriers share universe
`u`. The index object and morphism universes and the degree universe
`uι` are independent. The degree type is `ι : Type uι` and the shape
`c : ComplexShape ι` is arbitrary. Coefficient modules need not be
finite and deck-group orders need not be invertible in `R`.
No topology, continuity or smoothness hypothesis on the deck actions
is imposed.

## Constructed isomorphism and its maps

Write

```text
A = EquivariantDiagram D (ModuleCat.{u} R)
S = Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
F = etaleAssociatedVaryingSystemFunctor X Y hY
Fc = etaleAssociatedVaryingComplexFunctor X Y hY c
Fs = etaleAssociatedVaryingComplexSystemFunctor X Y hY c.
```

The last is a functor from coefficient complexes to `J ⥤
HomologicalComplex S c`. At a cover `j`, its terms are associated
sheaves of `(K.X n).action j`. Its differential is the actual
associated map of the evaluated coefficient differential. For
`a : i ⟶ j`, its transition chain map has degree component
`(etaleAssociatedTransition X Y hY a).app (K.X n)`.
These are the existing constructed maps, not new input.

For `q : ι`, `etaleAssociatedVaryingCoverwiseHomologyIso` has type

```text
Fs ⋙ (Functor.whiskeringRight J (HomologicalComplex S c) S).obj Hq_S
  ≅ Hq_A ⋙ F.
```

Thus its component at `K` and `j` is an actual sheaf isomorphism

```text
Hq_S((Fs.obj K).obj j) ≅ (F.obj (K.homology q)).obj j.
```

The component theorem
`etaleAssociatedVaryingCoverwiseHomologyIso_hom_app` gives its precise
factorization: the inverse of the existing
`etaleSheafHomologyEvaluationIso` at `Fc.obj K`, followed by evaluation
of `etaleAssociatedVaryingHomologyIso` at `K` and `j`. The first
identifies homology of the evaluated complex with evaluation of
diagram homology; the second identifies that diagram homology with
the associated coefficient homology diagram.

For `a : i ⟶ j`,
`etaleAssociatedVaryingCoverwiseHomologyIso_transition` states

```text
Hq_S((Fs.obj K).map a) ≫ e_K,j
  = e_K,i ≫
      (etaleAssociatedTransition X Y hY a).app (K.homology q).
```

For `f : K ⟶ L`,
`etaleAssociatedVaryingCoverwiseHomologyIso_naturality` states

```text
Hq_S((Fs.map f).app j) ≫ e_L,j
  = e_K,j ≫ (etaleAssociatedAt X Y j).map (Hq_A(f)).
```

Both have reassociated variants. Finally,
`etaleAssociatedVaryingComplexSystemFunctor_preserves_quasiIso`
proves that every coefficient quasi-isomorphism induces a
quasi-isomorphism of the associated sheaf complexes at each cover.

## Implemented proof

The definition first whisks `diagramHomologyIso` on the left by `Fc`,
then composes with `etaleAssociatedVaryingHomologyIso`. The
diagram-of-complexes presentation is definitionally `Fc` followed by
Mathlib's `complexOfFunctorsToFunctorToComplex`, so the resulting type
is the stated one. The component factorization is definitional.
The transition equation is naturality of the inner diagram
isomorphism; the coefficient-map equation evaluates naturality of the
outer isomorphism at `j`. For quasi-isomorphisms, use the proved
preservation by `Fc`, then Mathlib's
`HomologicalComplex.quasiIso_iff_evaluation` from
`Algebra/Homology/Functor.lean`, pinned at
`5ed2965256430c3649e86755f9576b54eca72435`.

## Retained scope

This is ordinary categorical homology of supplied coefficient and
sheaf complexes. It neither constructs a Shimura scheme, level tower
or its torsors nor identifies these inputs with Harris's geometric
objects. It makes no assertion about infinite-limit preservation,
global sections, compact support, derived completion, or smooth
group and Galois actions. Those obligations remain in the broader
Harris framework.
