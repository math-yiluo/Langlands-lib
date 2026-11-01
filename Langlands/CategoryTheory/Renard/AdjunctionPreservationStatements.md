# Renard A.V.2: adjoints preserve limits and colimits

This statement pair expresses the unnumbered preservation theorem in
Appendix A.V.2 of David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, printed p.260 / one-based
PDF266. A right adjoint preserves limits, and a left adjoint preserves
colimits. The declarations use Mathlib's actual adjunction, cones,
cocones and universal properties.

The namespace is `Langlands.Renard.AdjunctionPreservation`. The closed
aggregate `AdjunctionPreservationStatements` is exactly the ordered
conjunction

1. `RightAdjointPreservesLimitsStatement`;
2. `LeftAdjointPreservesColimitsStatement`.

All three declarations are definitions returning `Prop`. This file
supplies statements; it contains no proof of either component.

## Sources and formal packaging

The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The theorem is at A.V.2, printed p.260 / PDF266. The adjunction data
and triangle identities immediately preceding it are on printed
p.259 / PDF265, equations (A.V.2.1) and (A.V.2.2).

The supplementary older-edition author errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19 contain no correction to this preservation theorem. The
2026 original governs.

Renard writes `G : B → A` for the left adjoint and `F : A → B` for
the right adjoint. Mathlib's notation lists the left adjoint first,
so the actual hypothesis is `adj : G ⊣ F`. Its unit is
`𝟭 B ⟶ G ⋙ F` and its counit is `F ⋙ G ⟶ 𝟭 A`; both triangle
identities are part of `Adjunction`. Thus the hypothesis supplies
the adjunction itself.

The named closed propositions, the explicit quantification over a
supplied cone or cocone, the `Nonempty` wrappers and the ordered
conjunction are internal formal packaging of this theorem.
`IsLimit` and `IsColimit` are data-valued universal-property
structures; `Nonempty` expresses the existence of such data as a
proposition.

Renard's proof displays a Hom set into `lim (F ◦ D)` while establishing
that this target limit exists. The formal statement expresses the
conclusion directly on the image of the given limiting cone. In
particular, it concludes existence of a limit of `D ⋙ F` with vertex
`F.obj t.pt` without presupposing a target limiting object.
It also retains its actual legs, which determine the required
universal property. The dual statement does the same for colimits.

## Independent sizes and common data

Each component internally quantifies over

- `A : Type uA` with `[Category.{vA} A]`;
- `B : Type uB` with `[Category.{vB} B]`;
- functors `G : B ⥤ A`, `F : A ⥤ B` and actual `adj : G ⊣ F`;
- `I : Type uI` with `[Category.{vI} I]`.

The six universe levels `vA,uA,vB,uB,vI,uI` are independent in
each component and in the aggregate. There is no equality or
inequality constraint between the source, target or index sizes.
The indexing category may be empty, disconnected or infinite.
There are no completeness, cocompleteness, finiteness, additive or
abelian hypotheses.

## Right-adjoint limit preservation

`RightAdjointPreservesLimitsStatement` additionally binds an actual
diagram `D : I ⥤ A` and a cone `t : Cone D`. It asserts

```text
Nonempty (IsLimit t) → Nonempty (IsLimit (F.mapCone t)).
```

The image `F.mapCone t` is a cone on `D ⋙ F`. Its vertex is
`F.obj t.pt`; at `i : I`, its leg is
`F.map (t.π.app i) : F.obj t.pt ⟶ F.obj (D.obj i)`.
Its compatibility follows from that of `t` and the functor laws of
`F`.

The conclusion means that every cone `s` on `D ⋙ F` has a unique
map `s.pt ⟶ F.obj t.pt` whose composite with each image leg is
`s.π.app i`. The source cone's universal property is the premise.
No universal property of its image is assumed.

In particular, whenever a limit cone of `D` exists, its image is a
limit cone of `D ⋙ F`, so the latter limit exists at the stated
vertex. This is the preservation assertion, including the maps,
rather than merely an isomorphism between arbitrarily chosen objects.

## Left-adjoint colimit preservation

`LeftAdjointPreservesColimitsStatement` instead binds a diagram
`D : I ⥤ B` and a cocone `t : Cocone D`. It asserts

```text
Nonempty (IsColimit t) → Nonempty (IsColimit (G.mapCocone t)).
```

The image `G.mapCocone t` is a cocone on `D ⋙ G`. Its vertex is
`G.obj t.pt`; its leg at `i` is
`G.map (t.ι.app i) : G.obj (D.obj i) ⟶ G.obj t.pt`.
The conclusion supplies, for every cocone `s` on `D ⋙ G`, the
unique map `G.obj t.pt ⟶ s.pt` whose precomposition with every
image leg is `s.ι.app i`.

Thus an existing source colimit yields a target colimit with the
actual mapped vertex and inclusions. The statement assumes the
source universal property and concludes the target one.

## Scope

This pair covers only the preservation theorem in A.V.2. The Hom
bifunctor definition of adjoints, representability criterion,
uniqueness, unit–counit comparisons and scalar-extension example
remain separate source obligations. This pair does not claim
completion of A.V, Appendix A or the whole book.

The single imported module `Mathlib.CategoryTheory.Limits.IsLimit`
provides the actual data used in these statements, including the
adjunction and image-cone constructions. It introduces no replacement
functor or assumed preservation property. A future proof may reuse
Mathlib's adjunction-preservation results; that proof must target the
unchanged published aggregate.
