# Renard A.VI.3: simple quotients and simple subquotients

Author: Worker 6 (source reading, statement design, Lean draft and documentation).
Worker 961 independently rechecked the pair against PDF269–270 and the
2010 errata, compiled it, inspected the three complete declaration types
and exact bodies, and submitted it.

This statement unit gives the formal targets for the two-part unnumbered
Proposition in David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Appendix A.VI.3, printed page 264 / PDF270.
It introduces three Prop-valued definitions and no proofs of their claims.
The imported `CompositionChains`, `LocallyFiniteType` and
`RenardGrothendieckAxioms` Lean/Markdown pairs remain unchanged.

The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The full text of PDF269–270 and the rendered Proposition and proof on PDF270
were read. The common Grothendieck and AB6 hypotheses are introduced at the
end of PDF269, after the pure Jordan–Hölder theorem.

The public Appendix A discrepancy note
`notes/renard/appendix-a-corrections.md` treats other passages. No dedicated
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` was
found in the inspected workspace, project notes or pinned Library.
The supplementary registered 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was consulted at its Appendix A entries on PDF18–19. The entry for 2010
page 305 replaces an increasing sequence by a chain in the Zorn argument.
The governing 2026 passage already uses a chain. This bounded check does
not claim that all possible later errata have been found.

## Exact targets

All three declarations are in `Langlands.Renard`, with independent
universes `w`, `v`, `u` and actual parameters
`(C : Type u) [Category.{v} C] [Abelian C]`.

`FiniteTypeSimpleQuotientStatement.{w} C` is exactly

```lean
IsSourceGrothendieck.{w} C → SourceAB6 C →
  ∀ X : C, ¬ IsZero X → Langlands.Renard.IsFiniteTypeObject X →
    ∃ P : Subobject X, P < ⊤ ∧ Simple (cokernel P.arrow)
```

This is clause (i): a nonzero object of finite type has a simple quotient.
The witness `P` is an actual categorical subobject of `X`; `P < ⊤` says
that it is proper. Its quotient is the actual categorical cokernel of
`P.arrow : (P : C) ⟶ X`, with canonical quotient map `cokernel.π P.arrow`.
The abelian structure supplies that cokernel and makes its canonical
projection an epimorphism. There is no separately chosen quotient object
or quotient map.

`NonFiniteTypeSimpleSubquotientStatement.{w} C` is exactly

```lean
IsSourceGrothendieck.{w} C → SourceAB6 C →
  ∀ X : C, ¬ Langlands.Renard.IsFiniteTypeObject X →
    ∃ (A B : Subobject X) (h : A < B),
      Simple (cokernel (Subobject.ofLE A B h.le))
```

This is clause (ii): when `X` is not of finite type, there are subobjects
`A < B` whose quotient `B / A` is simple. `Subobject.ofLE A B h.le`
is the actual inclusion `(A : C) ⟶ (B : C)`. Its cokernel and canonical
cokernel projection are the actual subquotient and quotient map. The
strict inequality makes explicit that the two subobjects differ,
consistent with the source's simple, hence nonzero, quotient. The
conclusion imposes no finite-type condition on `B`, although the source
proof selects such a `B`.

`SimpleQuotientPropositionStatement.{w} C` is the conjunction

```lean
FiniteTypeSimpleQuotientStatement.{w} C ∧
  NonFiniteTypeSimpleSubquotientStatement.{w} C
```

Each clause contains its category hypotheses as antecedents inside the
proposition. The conjunction therefore expresses both claims in the same
source context; no Grothendieck or AB6 hypothesis is an ambient instance.
The `@[pp_with_univ]` attributes make the family bound visible in printed
declaration types.

## Source context and universes

The source assumes an abelian Grothendieck category and its AB6 local
finite-type condition for this Proposition. Both assumptions are retained
in both targets, including clause (i), whose Zorn argument only uses the
finite-type object's subobject unions and abelian quotient constructions.
No stronger standalone theorem with fewer category assumptions is
asserted by this unit.

`IsSourceGrothendieck.{w} C` is the published source convention: existence
of `w`-indexed coproducts together with the directed-subobject-sum
distributivity condition at that size. It includes no generator,
separator or local-smallness requirement. `SourceAB6 C` is the published
canonical local finite-type condition: for every object, the subset of
all actual finite-type subobjects has top as its least upper bound.
It is separate from the Grothendieck condition and is not Tohoku AB6.

Finite type is the unchanged published
`Langlands.Renard.IsFiniteTypeObject`, which includes existence of least
upper bounds for every subset of the actual subobject type and excludes
top as the least upper bound of a nonempty chain of proper subobjects.
It is not replaced by finite presentation, finite generation, a compact
object instance or a maximal-subobject condition.

The family universe `w` bounds the retained source Grothendieck predicate.
It does not bound the proper-subobject poset used by Zorn or the canonical
AB6 subset. The actual `Subobject X` lies in `Type (max u v)`; finite type
already provides unions over that whole type, and canonical AB6 also uses
it without shrinking. The targets therefore retain independent `w`, `v`
and `u`: they assert no `w`-smallness of subobjects and require no
construction of arbitrary `w`-indexed subobject sums in their conclusions.
The imported sized/canonical AB6 comparison only identifies their cover
formulations at `max u v`, not at arbitrary smaller `w`.

No `WellPowered`, `LocallySmall`, concrete-category, module,
finite-dimensionality, finite-length or Noetherianity condition is added.
Objects and subobjects are Mathlib's actual categorical objects and
subobjects. The latter's underlying objects and arrows use Mathlib's
existing chosen representatives.

## Proof boundary and provenance

For clause (i), the source applies Zorn to the nonempty poset of proper
subobjects of a nonzero object. Finite type ensures that the union of a
nonempty chain remains proper. A maximal proper subobject then gives a
simple cokernel quotient. For clause (ii), the source selects a finite-type
subobject using AB6 and applies clause (i). These are descriptions of the
source proof, not implemented Lean proofs.

The selection in clause (ii) must yield a nonzero finite-type subobject.
A future proof must first show that zero objects are finite type, so
nonfinite type implies nonzero. It must then derive a nonzero finite-type
subobject from the canonical AB6 cover: if every such subobject were zero,
the zero subobject would bound them all, contradicting their least upper
bound being the top subobject of a nonzero object. Transporting the
resulting quotient inside the selected subobject to two subobjects of `X`
is also a proof obligation. None of those intermediate facts is added as
a premise, an ambient instance or a conclusion of the present targets.
This explanation makes explicit an intermediate justification omitted
from the source's brief argument; it does not alter either source claim.

The three definitions are internal formal targets for the cited source
Proposition. Independent statement acceptance and publication must precede
a separate proof task against the exact published aggregate target.
Jordan–Hölder, numerical length, the following `JH` identities,
semisimplicity, module examples and finite-type comparisons remain separate
obligations. This file contains no new axioms or proof holes and claims
no theorem acceptance.
