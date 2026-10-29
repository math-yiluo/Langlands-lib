# Renard A.VI.3: identities for simple-subquotient classes

Author: Worker 6 (source reading, statement design, Lean draft and documentation).

This statement unit gives four Prop-valued definitions for the unnumbered
three-part Lemma in David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.VI.3, printed
page 264 / PDF270. It supplies targets and no proofs of the three claims.
Module: `Langlands.CategoryTheory.Renard.SimpleSubquotientIdentitiesStatements`;
namespace: `Langlands.Renard`. The imported `CompositionChains`,
`IndexedSubobjectSums`, `LocallyFiniteType` and
`RenardGrothendieckAxioms` Lean/Markdown pairs remain unchanged.

## Source and reading record

The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF269–270 were read in full, and the rendered Lemma and its proof on
PDF270 were checked visually. The source introduces the Grothendieck
and AB6 hypotheses at the end of PDF269, after the pure Jordan–Hölder
theorem. Those hypotheses continue through the preceding simple-quotient
Proposition and this Lemma.

The public discrepancy note `notes/renard/appendix-a-corrections.md`
concerns other passages. No dedicated
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md`
was found in the inspected workspace, project notes or pinned Library.
The supplementary registered 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at their Appendix A entries on PDF18–19. The nearby entry
for 2010 page 305 replaces an increasing sequence by a chain in the
preceding Zorn argument. No inspected entry corrects this Lemma. This
is a bounded check of supplementary errata for a different edition,
not a claim that all possible later errata have been found.

## Actual constructions

The source's `JH(X)` is the unchanged published
`simpleSubquotientClasses X : Set (ObjectClass C)`. A class `q` belongs
to it exactly when there are actual `A B : Subobject X` and `h : A ≤ B`
such that `cokernel (Subobject.ofLE A B h)` is simple and its
`objectClass` equals `q`. Thus these are isomorphism classes of all
simple actual subquotients, without a finite-length restriction.
`ObjectClass C` is the quotient of the actual objects of `C` by
isomorphism; it lies in the object universe.

For `P : Subobject X`, `(P : C)` is Mathlib's existing underlying
object and `P.arrow : (P : C) ⟶ X` its actual monomorphism. The quotient
in clause (i) is `cokernel P.arrow`, with canonical quotient projection
`cokernel.π P.arrow`. No separate quotient or projection is assumed.

For a supplied family `F : I → Subobject X`, the sum in clause (iii)
is the unchanged published `subobjectSum F`. It is the actual image
subobject of `Sigma.desc fun i => (F i).arrow`, the map from the
coproduct of the underlying objects into `X`. Its published intrinsic
laws identify it with the least upper bound of `Set.range F` in the
existing subobject order. The target uses this construction directly.

## Exact targets

Each declaration has the actual parameters
`(C : Type u) [Category.{v} C] [Abelian C]`. The family universe `w`,
Hom universe `v` and object universe `u` are independent.
The `@[pp_with_univ]` attributes keep `w` visible in printed types.

`SimpleSubquotientSubobjectQuotientStatement.{w} C` is exactly

```lean
IsSourceGrothendieck.{w} C → SourceAB6 C →
  ∀ (X : C) (P : Subobject X),
    simpleSubquotientClasses X =
      simpleSubquotientClasses (P : C) ∪
        simpleSubquotientClasses (cokernel P.arrow)
```

This is source clause (i): the simple-subquotient classes of an object
are the union of those of a subobject and its quotient. Both the zero
and top subobjects are included.

`SimpleSubquotientEmptyStatement.{w} C` is exactly

```lean
IsSourceGrothendieck.{w} C → SourceAB6 C →
  ∀ X : C, simpleSubquotientClasses X = ∅ ↔ IsZero X
```

This is clause (ii). Categorical `IsZero X` expresses the source's
`X = 0` independently of any chosen representative of a zero object.
The forward implication includes every object, and does not assume
that it has finite type or finite length.

`SimpleSubquotientSumStatement.{w} C` is exactly

```lean
∀ hG : IsSourceGrothendieck.{w} C, SourceAB6 C →
  letI : HasCoproducts.{w} C := hG.1
  ∀ (X : C) (I : Type w) (F : I → Subobject X),
    simpleSubquotientClasses (subobjectSum F : C) =
      ⋃ i, simpleSubquotientClasses (F i : C)
```

This is clause (iii). The first conjunct of the quantified `hG`
definitionally supplies source cocompleteness, namely
`HasCoproducts.{w} C`. The local `letI` uses that evidence for the
actual sum. The actual abelian structure supplies images. There is
no extra ambient coproduct instance or conditional choice of a least
upper bound in this target.

Every `I : Type w` is allowed, including the empty type. There is
no `Nonempty`, directedness, finiteness, finite-type, finite-length
or Noetherian premise on the family. For an empty family, the
published sum construction is the zero subobject and the union
on the right is empty. The identity for this case is included
in the target; this unit does not prove it.

`SimpleSubquotientIdentitiesStatement.{w} C` is exactly the conjunction

```lean
SimpleSubquotientSubobjectQuotientStatement.{w} C ∧
  SimpleSubquotientEmptyStatement.{w} C ∧
    SimpleSubquotientSumStatement.{w} C
```

Each component contains both source hypotheses as antecedents inside
the proposition. The aggregate keeps the order of the source clauses.

## Source context and size bounds

`IsSourceGrothendieck.{w} C` is the published source convention:
`w`-indexed coproducts and the directed-subobject-sum distributivity
condition at that size. It has no generator, separator or local-smallness
clause. `SourceAB6 C` is the separate canonical local finite-type
condition: for every object, all of its actual finite-type subobjects
have the top subobject as their least upper bound. This is the condition
in the source footnote, distinguished there from Tohoku AB6.

The common source context is retained even in clauses whose proofs
may need fewer hypotheses. No stronger standalone assertion is made
by omitting a source hypothesis from a component.

The size `w` bounds the retained source coproduct/AB5 data and the
supplied family `I`. It does not bound all subobjects. The actual
`Subobject X` lies in `Type (max u v)`. Canonical AB6 and the published
finite-type predicate use subsets of that whole actual type, without
shrinking. No assertion identifies this size with `w`. Finite subsets
of a supplied `I : Type w` can be indexed in `Type w`; the source's
reduction to finite partial sums therefore requires no indexing by
all subobjects and no extra size premise in clause (iii). The maps
and comparisons implementing that reduction remain proof obligations.

There is no `WellPowered`, `LocallySmall`, concrete-category,
module-category, finite-dimensionality, generator, separator or
complete-lattice premise.

## Source proof and proof boundary

The source calls clause (i) clear. Its categorical proof must compare
actual subquotients of a subobject and a quotient with those of the
ambient object, using the abelian subobject and quotient constructions.
No such comparison theorem is assumed by these targets.

For clause (ii), the source invokes the preceding simple-quotient
result. The nonzero direction needs a nonzero finite-type subobject
from AB6 and a simple quotient of it. A future proof must justify
that selection and its transport to an actual subquotient of the
ambient object; the target assumes no witness or nonzero-detection
lemma. The reverse direction excludes simple subquotients of a zero
object using categorical simplicity.

For clause (iii), the source first obtains the finite case from
clause (i), then replaces the family by its finite partial sums
to obtain a nonempty directed increasing family. The empty original
family can be treated separately or by including the empty partial
sum. For a simple quotient `M' / M''` of the total sum, if its class
occurred in no member, the source uses
`M' ∩ (M'' + M_i) = M''` for every index. AB5 then gives `M' = M''`,
contradicting simplicity. This describes the source route. It is
not an implemented Lean proof or a premise of the formal statements.

These four definitions are internal formal targets translating the
cited Lemma. Independent statement acceptance, publication and admission
to the current Library must precede a distinct exact proof successor.
The pure Jordan–Hölder theorem, the preceding simple-quotient Proposition,
numerical length, semisimplicity, supported subcategories, and the
module/localization branches remain separate obligations. This file
introduces no proof holes or new axioms and claims no theorem acceptance.
