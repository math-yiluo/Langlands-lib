# Renard A.IV: universal properties of inverse and direct systems

Author: Worker 695.

This pair proves the unchanged published
`Langlands.Renard.OrderedSystemLimit.OrderedSystemLimitStatements`
from [`OrderedSystemLimitStatements`](OrderedSystemLimitStatements.md).
The closing theorem is
`Langlands.Renard.OrderedSystemLimit.orderedSystemLimitStatements_proof`.
It is closed, with the three independent universe parameters `vC`, `uC`
and `uI`, and has exactly the published aggregate type. Its conjunction
is in inverse-then-direct order.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passages are A.IV.1 example 5 and the explicit direct-system
paragraph of A.IV.2, printed p.257 / one-based PDF263; the concrete
general universal property after (A.IV.1.2) is on printed p.256 / PDF262.
Both original pages were read in full. The supplementary 2010 author
errata, registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked on PDF18–19. Their PDF18 correction to old p.298 identifies
the direct limit with a colimit, as the governing 2026 text already does.
This is a bounded errata check.

The proof preserves the published correction of the inverse paragraph's
subscript interchange: for `i ≤ j` the inverse transition goes from
`D.obj (op j)` to `D.obj (op i)`. It also preserves the outward factor
map `t.pt ⟶ Y` fixed by the displayed colimit factorization, correcting
the source's reversed general colimit prose arrows.

The Lean proof is an internal expansion of the source's universal
property into actual Mathlib cones and cocones. It does not use the
source's auxiliary claim about morphisms between constant functors.
The statement pair and all its imports are unchanged.

For `inverseLimitStatement_proof`, first assume a witness `IsLimit t`
for the supplied cone `t`. Given a vertex `Y` and a compatible family
`q i : Y ⟶ D.obj (op i)`, form a competing cone `s` with point `Y`
and component at `i : Iᵒᵖ` equal to `q i.unop`. For an arbitrary arrow
`f : i ⟶ j`, `leOfHom f.unop` is the inequality `j.unop ≤ i.unop`.
The assumed family equation gives the required naturality equation.
Uniqueness of arrows in the order category identifies
`homOfLE (leOfHom f.unop)` with `f.unop`, and `Quiver.Hom.op_unop`
identifies its opposite with `f`; the constant functor's identity map simplifies
away. Thus no restriction to a special class of index morphisms occurs.
`IsLimit.existsUnique` gives the factor `l : Y ⟶ t.pt` and all its
leg equations. Evaluation at `op i` yields the stated equations, and
evaluation at `i.unop` transfers the stated uniqueness back to every
opposite-index object.

Conversely, assume the displayed family property. For every actual
cone `s`, take `q i = s.π.app (op i)`. The cone equation
`s.w (homOfLE h).op` supplies compatibility for each `h : i ≤ j`.
The family property supplies a unique map `s.pt ⟶ t.pt`.
Reindexing the equations and uniqueness over opposite objects gives
exactly the input to `IsLimit.ofExistsUnique`, constructing a universal
witness for `t`. The witness is then wrapped in `Nonempty`.

For `directLimitStatement_proof`, assume a witness `IsColimit t` and
form a competing cocone with point `Y` and legs the compatible family
`q i : D.obj i ⟶ Y`. For any order-category arrow `f : i ⟶ j`,
compatibility for `leOfHom f`, together with uniqueness of the
order-category arrow `homOfLE (leOfHom f) = f`, is
exactly naturality after simplifying the constant functor's identity.
`IsColimit.existsUnique` then gives the unique factor `t.pt ⟶ Y`
with `t.ι.app i ≫ l = q i` at every index. Conversely, the legs of any
actual cocone satisfy the family compatibility by
`s.w (homOfLE h)`. The assumed family property therefore supplies
precisely the input to `IsColimit.ofExistsUnique`, constructing and
wrapping a universal witness for the supplied `t`.

The final theorem pairs these two closed component proofs. The target
category has arbitrary object universe `uC` and morphism universe `vC`;
the order index has universe `uI`. The source's `PartialOrder` and
pairwise-upper-bound `IsDirectedOrder` hypotheses are retained exactly.
Directedness is unused by these universal-property equivalences, and
no index element is selected. Empty and infinite indices are therefore
included. For an empty index the equations are vacuous while the unique
factor maps remain quantified for every `Y`, retaining the terminal
and initial universal properties.

These equivalences characterize when a *supplied* cone or cocone is
universal. Neither direction assumes universal witnesses or unique
factorization as extra theorem inputs; each uses the corresponding
side of its implication. They do not assert that arbitrary diagrams
have limits or colimits. No additive, abelian, completeness or
nonemptiness assumption is added. General cone bridges, elementary
shapes, intersections/unions, abelian-category existence and concrete
abelian-group constructions remain separate work. This proof makes
no claim of completing A.IV, Appendix A or the whole-book program.
