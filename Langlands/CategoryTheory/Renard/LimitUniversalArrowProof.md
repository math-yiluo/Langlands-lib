# Proof: limits and colimits as universal arrows for the diagonal

This module proves `Langlands.Renard.LimitUniversalArrow.LimitUniversalArrowStatements`
from `Langlands.CategoryTheory.Renard.LimitUniversalArrowStatements`, the
statement unit for the remark on printed p.256 / PDF262 and the sentence on
printed p.257 / PDF263 of David Renard, *Représentations des groupes réductifs
p-adiques* (9 July 2026), Appendix A.IV. The statement Markdown records the
source correspondence and the arrow corrections; this file describes only the
implemented Lean proof. All theorems keep the independent universe levels
`vJ vC uJ uC` and add no hypothesis on the index category.

The equivalence converses and the comma-category formulations are internal
derived formulations of the source's one-directional remarks, as explained in
the published statement Markdown. The proof retains morphisms of `C` as the
unique factors: `Y ⟶ X` for a limit and `X ⟶ Y` for a colimit. It never needs
to identify all transformations between constant functors with those morphisms.
Every cone and cocone keeps its vertex explicitly; componentwise equations and
transformation extensionality apply to empty and disconnected index categories
as well. No nonemptiness, connectedness, size or existence-of-limits premise is
introduced.

Worker 709 authored the shared proof draft. Worker 1193 checked the original
source correspondence and prepared this proof pair for submission with that
coauthorship retained.

## Factorization forms

`limitFactorization : LimitFactorizationStatement` is proved directly.

- From `h : IsLimit (Cone.mk X η)`, given `Y` and `f : ΔY ⟶ D`, the factor is
  `h.lift (Cone.mk Y f)`. Its equation `(diagonal J C).map g ≫ η = f` is
  checked componentwise with `NatTrans.ext` and `h.fac`. Uniqueness applies
  `h.uniq` to a competitor `g`, whose component equations are obtained from
  the transformation equation by evaluating at each index (`NatTrans.app`).
- Conversely, `IsLimit.ofExistsUnique` builds the limit witness: for a cone
  `s`, the hypothesis at `s.pt` and `s.π` gives the unique `g`, its component
  equations follow by evaluation, and uniqueness follows by transformation
  extensionality from the componentwise equations of a competitor.

`colimitFactorization : ColimitFactorizationStatement` is the same argument
with `IsColimit.desc`, `IsColimit.fac`, `IsColimit.uniq` and
`IsColimit.ofExistsUnique`, applied to `Cocone.mk Y f` and `η ≫ Δg`.

## Structured-arrow forms

`limitUniversal : LimitUniversalStatement` composes `limitFactorization` with
the published `Langlands.Renard.UniversalArrow.leftCharacterization_proof`,
instantiated at the categories `C` and `J ⥤ C`, the functor `diagonal J C`,
the object `D` and the arrow `η`. That theorem identifies the left
factorization property with `Nonempty (CostructuredArrow.IsUniversal ...)`.

`colimitUniversal : ColimitUniversalStatement` composes `colimitFactorization`
with `Langlands.Renard.UniversalArrow.rightCharacterization_proof`, which
identifies the right factorization property with
`Nonempty (StructuredArrow.IsUniversal ...)`.

`limitUniversalArrowStatements` is the anonymous-constructor conjunction of
the four theorems, in the order of the aggregate statement.

## Checks

Diagnostic `5798f310-ae3e-4de5-8f8c-87b3d2f0109c` compiled the statement and
proof modules with zero diagnostics in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` and inspected
`limitUniversalArrowStatements`: its axioms are `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry` and no new axiom.
