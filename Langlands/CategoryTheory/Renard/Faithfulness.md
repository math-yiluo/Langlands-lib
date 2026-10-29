# Renard A.VIII.1: proof of the faithfulness criteria

Authors: Worker 6 (Lean proof and original companion), Worker 912
(independent source and interface verification, type inspection and
submission edits to this companion).

This proof unit proves the published
`Langlands.Renard.FaithfulnessCriteriaStatement` from
`Langlands.CategoryTheory.Renard.FaithfulnessStatements`. The target and its
imported exactness definitions in
`Langlands.CategoryTheory.RenardExactFunctor` are unchanged.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, A.VIII.1, printed
page 266 / PDF page 272, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 6 reread the full page as extracted text and as a rendered image on
28 October 2026. Worker 912 independently verified the fingerprint and the
296-page count and reread the extracted text of PDF page 272 on
28 October 2026. The available supplementary 2010 errata appendix tail
was also reread by Worker 6: its correction replaces faithfulness by
exactness when asserting preservation of epimorphisms and monomorphisms.
The governing 2026 paragraph already uses exactness. The statement
companion records the full original and supplementary source locations.

## Theorem signatures

The shared context retains arbitrary abelian categories `C : Type u₁`
and `D : Type u₂`, `Category.{v₁} C`, `Category.{v₂} D`, the actual functor
`F : C ⥤ D` and `[F.Additive]`. All four universes are independent.
With `open CategoryTheory` and `open CategoryTheory.Limits`, the complete
shared context and three theorem signatures are

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

theorem faithfulZeroMorphismCriterion :
  FaithfulZeroMorphismCriterionStatement F

theorem sequenceExactReflectsZeroFaithful :
  SequenceExactReflectsZeroFaithfulStatement F

theorem faithfulnessCriteria :
  FaithfulnessCriteriaStatement F
```

All declarations are in namespace `Langlands.Renard`, module
`Langlands.CategoryTheory.Renard.Faithfulness`. The statement companion
gives the complete proposition bodies. In particular, the sequence exactness
and zero-object reflection hypotheses remain antecedents of the second
clause; none is a parameter of the aggregate. There is no smallness,
concreteness, module-category, representation or finiteness assumption.

## Zero-morphism criterion

The implemented proof of `faithfulZeroMorphismCriterion` uses the actual
Hom maps. Faithfulness implies zero-morphism reflection by
`Functor.zero_of_map_zero` (Mathlib
`CategoryTheory/Limits/Preserves/Shapes/Zero.lean`), using the zero-morphism
preservation that additivity supplies. Conversely, if
`F.map f = F.map g`, then `Functor.map_sub` gives `F.map (f - g) = 0`;
reflection gives `f - g = 0`, hence `f = g` by `sub_eq_zero`. This proves
`F.Faithful` directly from its `map_injective` field. The sufficient
direction is the source assertion. Necessity is the elementary derived
converse already included in the target.

## Exactness and zero-object reflection

The implemented proof of `sequenceExactReflectsZeroFaithful` follows
Renard's image argument. A short exact complex `S` satisfies `S.Exact`
together with `Mono S.f` and `Epi S.g`, so it is an instance of both
one-sided sequences in the published `SequenceExact F`. Applying the left
and right components of that hypothesis to such complexes supplies the
inputs of Mathlib's `Functor.preservesMonomorphisms_of_preserves_shortExact_left`
and `Functor.preservesEpimorphisms_of_preserves_shortExact_right`
(`Algebra/Homology/ShortComplex/ExactFunctor.lean`). These give local
instances that `F` preserves monomorphisms and epimorphisms. They are
conclusions from the sequence conditions, not extra premises.

For an actual arrow `f` with `F.map f = 0`, use the abelian image
factorization `Abelian.factorThruImage f ≫ Abelian.image.ι f = f`
(`Abelian.image.fac` in `CategoryTheory/Abelian/Images.lean`). The first
arrow is epi and the second mono in an abelian category; this is the
source's factorization `X → I → Y`. The mapped inclusion is mono, so
`zero_of_comp_mono` shows that the mapped image projection is zero. That
mapped projection is epi, so `IsZero.of_epi_eq_zero` shows that
`F.obj (Abelian.image f)` is a zero object. The reflection antecedent
gives `IsZero (Abelian.image f)`. Every arrow out of a zero object is zero
(`IsZero.eq_zero_of_src`), so rewriting `f` by its factorization yields
`f = 0`. The first criterion now gives faithfulness.

## Aggregate

The theorem `faithfulnessCriteria` pairs the two named clause proofs in
the exact target order. The conjunction is derived packaging.
The proof uses the pinned Mathlib interfaces directly and does not depend
on the unpublished finite-preservation or homology proof branches.

## Development evidence

At pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, Worker 6 reported clean Lake
build and inspection runs `86f3953b-360b-41f0-89ce-c73735e881e5` and
`8d91099a-187e-4147-8bf8-cc11abd21e5c`. Worker 912 independently repeated
equivalent checks. Lake build and aggregate inspection
`c9fad9c4-88e1-4562-85e8-55773776e883` completed with zero errors or
warnings. The aggregate has exactly the independent levels
`v₁, v₂, u₁, u₂` and standard axioms `propext`, `Classical.choice` and
`Quot.sound`. Its complete type fingerprint is
`ced40c3887b655ea667fd00da205d9f39cfcf83888bf011005a8949d2dc890a6`.
Check `99a6b51e-d8e4-42db-8dc1-6316b0048743` printed the three unapplied
types with explicit universes. It assigned each unapplied constant to the
complete target telescope above. It also assigned the aggregate to the
unfolded conjunction of the two proposition bodies. All passed with zero
errors or warnings.

These development checks establish compilation only. Independent semantic
review, Lake build, exact-target validation and publication remain
required. This unit supplies no proof of a finite-preservation, homology
or Hom-object-property statement, and claims no whole-book completion.
