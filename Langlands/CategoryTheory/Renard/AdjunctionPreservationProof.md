# Renard A.V.2: proof that adjoints preserve limits and colimits

Worker 1172 proves the published closed proposition
`Langlands.Renard.AdjunctionPreservation.AdjunctionPreservationStatements.{vA,uA,vB,uB,vI,uI}`,
imported from `Langlands.CategoryTheory.Renard.AdjunctionPreservationStatements`.
The final theorem is
`Langlands.Renard.AdjunctionPreservation.adjunctionPreservationStatements_proof`.
Its type is exactly the closed aggregate at the six independent universe
levels `vA,uA,vB,uB,vI,uI`. It has no extra assumptions or parameters.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The unnumbered theorem and its proof are in A.V.2, printed p.260 / one-based
PDF266. The adjunction morphisms and the triangle identities (A.V.2.1) and
(A.V.2.2) are on printed p.259 / PDF265. These pages were read for this
proof. The older-edition author errata `renard-2010-corrections-complements`,
PDF18–19, correct nearby passages of the 2010 edition but not this
theorem. The statement companion explains the source-to-Lean formulation,
including Renard's names `G : B → A` for the left adjoint and `F : A → B` for
the right adjoint. The hypothesis is therefore Mathlib's `adj : G ⊣ F`.

## Implemented proof

The module imports `Mathlib.CategoryTheory.Adjunction.Limits` and the
unchanged statement module. It contains three theorems.

### Right adjoints and limits

`rightAdjointPreservesLimitsStatement_proof` introduces `A`, `B`, the functors
`G` and `F`, the adjunction `adj : G ⊣ F`, the index category `I`, the
diagram `D : I ⥤ A` and the supplied cone `t : Cone D`. It then destructs
the premise `Nonempty (IsLimit t)`, which yields actual limit data
`ht : IsLimit t`. This step is allowed because the goal is a proposition.

Mathlib's `Adjunction.rightAdjoint_preservesLimits`, applied to `adj`, gives
the local fact `hF : PreservesLimitsOfSize.{vI, uI} F`. The universes are
those of the supplied index category. The proof projects `hF` directly,
without instance search. The field `preservesLimitsOfShape` at
`I` is followed by `preservesLimit` at `D`. The resulting field `preserves`,
applied to `ht`, has type `Nonempty (IsLimit (F.mapCone t))`, which is the
goal. Hence the conclusion concerns the actual image cone, with vertex
`F.obj t.pt` and legs `F.map (t.π.app i)`.

The Mathlib lemma constructs this universal property; it does not assume
it. `Adjunction.functorialityAdjunction'` shows that the functor
`Cone.functoriality D F : Cone D ⥤ Cone (D ⋙ F)` has a left adjoint
`Adjunction.functorialityLeftAdjoint`. That left adjoint sends a cone `s`
on `D ⋙ F` to the cone on `D` with vertex `G.obj s.pt` and legs
`G.map (s.π.app i) ≫ adj.counit.app (D.obj i)`. Next,
`IsLimit.isoUniqueConeMorphism` turns `ht` into a unique cone morphism from
this transported cone to `t`. The cone-level adjunction gives a bijection
between cone morphisms `s ⟶ F.mapCone t` and cone morphisms from the
transported cone to `t`. `Equiv.unique` then transfers uniqueness, and
`IsLimit.isoUniqueConeMorphism` converts the result back into
`IsLimit (F.mapCone t)`. This is Renard's chain

```text
Hom(Y, F(lim D)) = Hom(G(Y), lim D) ≃ Hom(Δ G(Y), D) ≃ Hom(Δ Y, F ∘ D)
```

stated on cones, so the identifications respect the given legs. Renard applies
the principle A.III.3; here the universal property of `F.mapCone t` is
checked directly against every cone `s`.

### Left adjoints and colimits

`leftAdjointPreservesColimitsStatement_proof` is dual. It introduces the same
data, a diagram `D : I ⥤ B` and a cocone `t : Cocone D`, and destructs
`Nonempty (IsColimit t)` to obtain `ht : IsColimit t`.
`Adjunction.leftAdjoint_preservesColimits` gives the local fact
`hG : PreservesColimitsOfSize.{vI, uI} G`. Its fields `preservesColimitsOfShape`,
`preservesColimit` and `preserves`, applied to `ht`, have type
`Nonempty (IsColimit (G.mapCocone t))`, with vertex `G.obj t.pt` and legs
`G.map (t.ι.app i)`.

Mathlib's proof uses `Adjunction.functorialityAdjunction`. This adjunction
makes `Cocone.functoriality D G` left adjoint to
`Adjunction.functorialityRightAdjoint`, which sends a cocone `s` on `D ⋙ G`
to the cocone on `D` with vertex `F.obj s.pt` and legs
`adj.unit.app (D.obj i) ≫ F.map (s.ι.app i)`. Then
`IsColimit.isoUniqueCoconeMorphism` and `Equiv.unique` transfer the unique
cocone morphism out of `t` to a unique cocone morphism from
`G.mapCocone t` to every cocone `s`. `IsColimit.isoUniqueCoconeMorphism`
converts this back into `IsColimit (G.mapCocone t)`.

### The aggregate

`adjunctionPreservationStatements_proof` pairs the two component proofs in
the published order: limits first, then colimits.

## Role of the `Nonempty` wrappers

`IsLimit` and `IsColimit` are data-valued structures, so the statements wrap
them in `Nonempty`. Since each component's conclusion is a proposition, the
premise may be destructed to obtain the actual data. Mathlib's
`PreservesLimit` and `PreservesColimit` are `Prop`-valued classes whose
`preserves` fields return the required `Nonempty` directly. Inside these
fields Mathlib constructs the actual `IsLimit` or `IsColimit` data described
above. Hence no extra wrapping, choice of a target limit or preservation
certificate is supplied as an input.

## Generality

The Mathlib lemmas are in the `ArbitraryUniverse` section of
`Mathlib/CategoryTheory/Adjunction/Limits.lean`. Their object, morphism and
index universes are unrelated, and they assume no existence of limits or
colimits. The index category may be empty, disconnected or infinite. For an
empty index the theorem says that the right adjoint preserves terminal objects
and the left adjoint preserves initial objects.

The complete-declaration inspections of all three theorems report kind
`theorem`, level parameters `[vA, uA, vB, uB, vI, uI]` and only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The module compiles
with no errors or warnings. The statement pair and its import are unchanged.

## Scope

This proves only the A.V.2 preservation theorem. The Hom-bifunctor
definition, representability criterion, uniqueness of adjoints, unit–counit
comparisons and scalar-extension example of A.V remain separate obligations.
This proof does not complete A.V, Appendix A or the whole book.
