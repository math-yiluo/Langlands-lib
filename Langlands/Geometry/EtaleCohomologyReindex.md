# Reindexing compatible coefficient and cohomology diagrams

This file constructs restriction along an index functor for the compatible
coefficient diagrams of `EtaleCohomologyDiagramFunctor`. It proves compatibility
with the existing ordinary cohomology and global-section functors.

## Parameters and variance

Fix a commutative ring `R : Type u`, a category `J : Type v` with morphisms in
universe `w`, and `S : J ⥤ Scheme.{u}ᵒᵖ`. Every scheme morphism
`(S.map a).unop` is assumed étale. Write `X_i = (S.obj i).unop`.
An arrow `a : i ⟶ j` therefore determines `f_a : X_j ⟶ X_i`.
Coefficients are actual small-étale sheaves of `ModuleCat.{u} R` objects, with
maps `f_a* D_i ⟶ D_j` obeying the previously defined restriction laws.

Let `K : Type v'` have morphisms in universe `w'`, and let `F : K ⥤ J`.
The universes of the two index categories are independent. No fullness,
faithfulness, finality, filteredness, or geometric hypothesis on `F` is needed.
The scheme diagram is now `F ⋙ S`; its arrows are étale because they are arrows
already covered by the hypothesis on `S`.

## Transport and the reindexing functor

All declarations below, except the étaleness instance, lie in
`Langlands.Geometry.EtalePullback.CoefficientDiagram`.

`map_id_transport` restates a coefficient diagram's identity law for an arrow
`a : i ⟶ i` equipped with an equality `a = 𝟙 i`. It uses `restrictionCongr`
for the resulting equality of scheme arrows, followed by `restrictionId`.
`map_comp_transport` similarly restates composition for arrows `a`, `b`, and
`c` with `c = a ≫ b`. The proof of each lemma eliminates the equality and
uses the original coefficient law. These lemmas handle equality transport in
the dependent sheaf types; they do not assume additional compatibility.

`reindex F D` has objects and transition maps

```text
(reindex F D).obj i = D.obj (F.obj i)
(reindex F D).map a = D.map (F.map a).
```

Its identity and composition laws apply the two transport lemmas to
`F.map_id` and `F.map_comp`. The equality proofs inside `restrictionCongr`
agree by proof irrelevance once their endpoints are identified.

For a compatible morphism `α : D ⟶ E`, `reindexMap F α` has component
`α.app (F.obj i)`. Its compatibility is exactly `α.comm (F.map a)`.
`reindexFunctor F` assembles these constructions into a functor

```text
CoefficientDiagram R S ⥤ CoefficientDiagram R (F ⋙ S).
```

Its functor laws follow from componentwise identity and composition in the
coefficient categories.

## Cohomology, sections, and degree zero

For each natural-number degree `q`, `reindex_cohomology` proves

```text
(reindex F D).cohomology q = F ⋙ D.cohomology q.
```

`reindex_sections` proves the corresponding equality for ordinary global
sections. Both are definitional equalities: they use the same sheaf objects,
the same restriction and coefficient maps, and the same constructions from
the imported functor module.

`reindexCohomologyFunctorIso` packages the first comparison naturally in `D`:

```text
reindexFunctor F ⋙ cohomologyFunctor q
  ≅ cohomologyFunctor q ⋙ (Functor.whiskeringLeft K J (ModuleCat R)).obj F.
```

`reindexSectionsFunctorIso` is the analogous comparison for `sectionsFunctor`.
Both are reflexive isomorphisms between definitionally equal functors. Their
components are identities, and naturality includes all compatible coefficient
morphisms, not only the objects.

Finally, `reindex_cohomologyZeroIso_hom_app` proves that the canonical comparison
from degree-zero cohomology to sections at vertex `i` of the reindexed diagram
is precisely the original comparison at `F.obj i`.

## Provenance and retained specialization

This is an internal categorical construction. It uses the actual sheaves,
restriction functors, derived cohomology, and ordinary sections from the
imported project modules, together with Mathlib's precomposition functor.
The transport proofs and pointwise formulas above justify the construction;
no named theorem from the literature is asserted.

The construction permits restriction of a supplied level diagram to another
index category, once its schemes, étale transition maps, and compatible
coefficient sheaves have been constructed. The actual Harris Shimura tower and
its coefficient maps remain required geometric input. This file does not
construct that tower, assert cofinality or a limit comparison, change scalars,
provide compact support, or identify the separate scheme-automorphism action.
