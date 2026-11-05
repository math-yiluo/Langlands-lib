# Renard A.IV.1–A.IV.2: limits and colimits as universal arrows for the diagonal

This is a statement-only unit for two sentences of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.IV:

- the remark following the definition of a limit, printed p.256 / one-based
  PDF262: "On voit que (ΔX, η) est solution du problème universel à gauche
  posé par Δ et D";
- the sentence following the definition of a colimit, printed p.257 /
  PDF263: "Une colimite est solution du problème universel à droite posé par
  Δ et D".

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF257 (the A.III.1 definition of right and left universal
problems) and PDF262–263 directly from that file.

## Exact declarations and hypotheses

The namespace is `Langlands.Renard.LimitUniversalArrow`, in module
`Langlands.CategoryTheory.Renard.LimitUniversalArrowStatements`. Each
component is a closed `Prop`-valued definition. It universally quantifies an
index category `J : Type uJ` with `Category.{vJ} J`, a category
`C : Type uC` with `Category.{vC} C`, a diagram `D : J ⥤ C`, an object
`X : C` and a transformation `η` between `D` and the constant functor at
`X`. The four universe levels are independent. No hypothesis is placed on
`J`: it may be empty, disconnected or large. `diagonal J C` is the published
`Langlands.CategoryTheory.Renard.diagonal`, an abbreviation of Mathlib's
actual `Functor.const J : C ⥤ (J ⥤ C)`.

1. `LimitUniversalStatement` takes `η : (diagonal J C).obj X ⟶ D` and asserts
   `Nonempty (IsLimit (Cone.mk X η))` iff
   `Nonempty (CostructuredArrow.IsUniversal (CostructuredArrow.mk η))`,
   where the costructured arrow is taken for the functor `diagonal J C` and
   the object `D` of `J ⥤ C`.
2. `LimitFactorizationStatement` takes the same data and asserts
   `Nonempty (IsLimit (Cone.mk X η))` iff for every `Y : C` and every
   `f : (diagonal J C).obj Y ⟶ D` there is a unique `g : Y ⟶ X` with
   `(diagonal J C).map g ≫ η = f`.
3. `ColimitUniversalStatement` takes `η : D ⟶ (diagonal J C).obj X` and
   asserts `Nonempty (IsColimit (Cocone.mk X η))` iff
   `Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk η))`, for the
   structured arrow from `D` to the functor `diagonal J C`.
4. `ColimitFactorizationStatement` takes the same data and asserts
   `Nonempty (IsColimit (Cocone.mk X η))` iff for every `Y : C` and every
   `f : D ⟶ (diagonal J C).obj Y` there is a unique `g : X ⟶ Y` with
   `η ≫ (diagonal J C).map g = f`.

`LimitUniversalArrowStatements.{vJ,vC,uJ,uC}` is the conjunction of these four
propositions, in that order. It has no parameters of its own.

## Correspondence with the source

Renard's `I`, `𝒞`, `Δ`, `D`, `ΔX` and `η` are `J`, `C`, `diagonal J C`, `D`,
`(diagonal J C).obj X` and `η`. A limit in the source is "la donnée d'un
foncteur constant ΔX ... et d'une transformation naturelle η de ΔX vers D";
it is represented here by Mathlib's actual cone `Cone.mk X η`, which keeps the
vertex `X` as a field. Being a limit or colimit is Mathlib's `IsLimit` or
`IsColimit`; these carry factorization data, so `Nonempty` turns their
existence into a proposition.

The A.III.1 definition on printed p.251 / PDF257 says that `X` and
`j : F(X) → Y` solve the left universal problem posed by `F` and `Y` if for
every `Z` and every `f : F(Z) → Y` there is a unique `g : Z → X` with
`j ∘ F(g) = f`; the right problem is dual, with `i : Y → F(X)` and
`F(g) ∘ i = f`. Taking `F = Δ` (from `C` to `J ⥤ C`) and the object `D` of
`J ⥤ C`, these are exactly the right-hand sides of clauses 2 and 4. Renard
writes composition in function order: Lean's `(diagonal J C).map g ≫ η = f`
is `η ∘ Δ(g) = f`, and `η ≫ (diagonal J C).map g = f` is `Δ(g) ∘ η = f`.
Clauses 1 and 3 restate the same remarks with Mathlib's comma-category
universal arrows: `CostructuredArrow.IsUniversal` abbreviates terminality
(left problem) and `StructuredArrow.IsUniversal` abbreviates initiality
(right problem). They match the conventions of the published A.III.1
statements `Langlands.Renard.UniversalArrow.LeftCharacterizationStatement`
and `RightCharacterizationStatement`.

The source's two sentences assert only that a limit (colimit) is a solution.
Each clause here is an equivalence; the converse direction, that every
solution of the universal problem is a limit (colimit), is part of the
formulation. This is a derived strengthening, not a claim attributed to the
book.

## Corrections reflected in the formulation

The limit definition on PDF262 quantifies over "une unique transformation
naturelle ΔY → ΔX (c'est-à-dire un unique morphisme X → Y)". The parenthetical
arrow is reversed, and the colimit definition on PDF263 reverses both of its
prose arrows. Both points, and the failure of the source's claim that
transformations between constant functors correspond to morphisms for every
nonempty index category, are documented in `notes/renard/appendix-a-corrections.md`
and in the published `Langlands/CategoryTheory/Renard/ConeBridge.md`.

Consistently with those corrections, the factorization clauses quantify over
morphisms `g : Y ⟶ X` (respectively `g : X ⟶ Y`) of `C`, as the A.III.1 problem
posed by `Δ` and `D` does, and not over arbitrary transformations between
constant functors; the correction note explains why limits over arbitrary
index categories must be stated with morphisms. No connectedness or
nonemptiness assumption is added. The vertex `X` remains explicit, which matters for an
empty index.

The published ConeBridge unit already proves the componentwise form
`coneUniversal_iff_nonempty_isLimit` (A.IV.1.2) and its dual. The present
clauses instead use the single transformation equation of the A.III.1
problem and the structured-arrow formulation. They connect the A.IV
definitions to the earlier universal-arrow terminology, which
`notes/renard/limits-colimits-progress.md` lists as a retained obligation.

## Proof boundary

This file supplies proposition definitions and no proof of them. The
uniqueness of limits up to unique isomorphism, the Hom isomorphism
(A.IV.1.1), the examples of A.IV.1 and A.IV.2, and existence of limits are
outside this unit; several are covered by the published ConeBridge unit and
the A.III.1 comparison statements. After independent acceptance and
publication, a separate exact-proof task can target
`LimitUniversalArrowStatements` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
