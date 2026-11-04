# Renard A.III.1: the diagonal and binary products and coproducts

Author: Worker 709.

This statement-only unit records Appendix A.III.1, example 1, of David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, printed p.252 / one-based PDF258, using the universal
problem definition on printed p.251 / PDF257. It also compares these
universal arrows with the binary limit and colimit formulations in A.IV.1,
example 3, and A.IV.2, printed p.257 / PDF263. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original PDF257–258 and PDF262–263 were read directly for this unit.

The [Appendix A discrepancy note](../../../notes/renard/appendix-a-corrections.md)
does not change example 1. Its correction of the general colimit prose
agrees with the outward factor maps used below. The older-edition
supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF18–19. That bounded reading gives no correction to this
binary-diagonal example.

## Actual objects and hypotheses

All declarations lie in `Langlands.Renard.BinaryDiagonal`. Each component
is a closed proposition quantifying an arbitrary category `C : Type uC`
with `Category.{vC} C`. The object universe `uC` and morphism universe `vC`
are independent. No smallness, additivity, zero-object, completeness or
existence assumption is imposed.

The functor is Mathlib's actual `Functor.diag C : C ⥤ C × C`, taking an
object `Z` to `(Z,Z)` and a morphism `l` to `(l,l)`. The codomain is the
product category. `CategoryTheory.Prod.mkHom p q` forms the actual pair of
morphisms; composition in this category is componentwise.

For products, the supplied data are `X Y P : C`, `p : P ⟶ X` and
`q : P ⟶ Y`. Their pair is an arrow from the diagonal of `P` to `(X,Y)`.
`CostructuredArrow.mk (S := Functor.diag C)` places this arrow in the
actual costructured-arrow category. Its `IsUniversal` is terminality data,
corresponding to Renard's left universal problem.

For coproducts, the supplied data are `X Y Q : C`, `i : X ⟶ Q` and
`j : Y ⟶ Q`. Their pair is an arrow from `(X,Y)` to the diagonal of `Q`.
`StructuredArrow.mk (T := Functor.diag C)` places this arrow in the actual
structured-arrow category. Its `IsUniversal` is initiality data,
corresponding to Renard's right universal problem.

The corresponding `BinaryFan.mk p q` and `BinaryCofan.mk i j` are actual
cones and cocones over Mathlib's discrete walking-pair diagram
`pair X Y`. The fan has vertex `P` and projections `p,q`; the cofan has
vertex `Q` and inclusions `i,j`. `IsUniversal`, `IsLimit` and `IsColimit`
carry witness data. Every occurrence is wrapped in `Nonempty` to express
existence of those data as a proposition.

## Four component statements

1. `ProductFactorizationStatement` says that the paired arrow `(p,q)` is
   universal on the left for the diagonal if and only if for every
   `Z : C`, `f : Z ⟶ X` and `g : Z ⟶ Y` there exists a unique
   `l : Z ⟶ P` satisfying both `l ≫ p = f` and `l ≫ q = g`.
2. `ProductLimitStatement` says that the same left universal property is
   equivalent to `Nonempty (IsLimit (BinaryFan.mk p q))`.
3. `CoproductFactorizationStatement` says that the paired arrow `(i,j)` is
   universal on the right for the diagonal if and only if for every
   `Z : C`, `f : X ⟶ Z` and `g : Y ⟶ Z` there exists a unique
   `l : Q ⟶ Z` satisfying both `i ≫ l = f` and `j ≫ l = g`.
4. `CoproductColimitStatement` says that the same right universal property
   is equivalent to `Nonempty (IsColimit (BinaryCofan.mk i j))`.

`BinaryDiagonalStatements.{vC,uC}` is the conjunction of these four closed
components in that order. Uniqueness in each factorization ranges over
morphisms satisfying both displayed equations. The statements characterize
the supplied arrows and assert no general existence of products or
coproducts.

## Source correspondence and derived packaging

Renard defines the product as a left solution and the coproduct as a right
solution for the diagonal and the fixed pair `(X,Y)`. Substitution of the
actual diagonal into the A.III.1 definition gives, respectively,
`(l,l) ≫ (p,q) = (f,g)` and `(i,j) ≫ (l,l) = (f,g)`. Componentwise
composition gives exactly the equations in the first and third
statements. Lean's `a ≫ b` denotes the source's `b ∘ a`.

The second and fourth statements combine this example with the source's
binary discrete-diagram product assertion in A.IV.1 and its coproduct
dual in A.IV.2. These explicit equivalences with Mathlib's binary
witnesses, the `Nonempty` wrappers, independent universes and the closed
conjunction are derived formal packaging. They are not presented as
separately numbered results in the book.

The existing [universal-arrow statements](UniversalArrowStatements.md)
and their published proof give the generic factorization dictionary.
The [elementary limit and colimit statements](ElementaryLimitColimitStatements.md)
and their published proof include arbitrary fans and cofans. This unit
records the comparison using the actual diagonal, paired arrow and
binary fan or cofan, so all chosen structure maps remain visible.

## Proof boundary

This file defines propositions and supplies no proof. A separate exact
proof can reuse the generic universal-arrow characterization together
with componentwise product-category equality and the existing binary
fan/cofan universal-property API. That is a possible proof route, not
proof evidence. The exact-proof successor targets
`Langlands.Renard.BinaryDiagonal.BinaryDiagonalStatements` only after
independent statement acceptance and actual Library publication, in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

The completion of the other A.III examples and the whole appendix
remains with the parent book program.
