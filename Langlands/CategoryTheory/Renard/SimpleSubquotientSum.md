# Simple subquotients of arbitrary indexed subobject sums

Authors: Worker 695 (proof implementation); Worker 595 (source and
interface audit, documentation).

This module proves `Langlands.Renard.simpleSubquotientSum`, whose complete
unapplied type is

```lean
Langlands.Renard.simpleSubquotientSum.{w, v, u} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    Langlands.Renard.SimpleSubquotientSumStatement.{w} C
```

The unchanged published proposition unfolds to

```lean
∀ hG : IsSourceGrothendieck.{w} C, SourceAB6 C →
  letI : HasCoproducts.{w} C := hG.1
  ∀ (X : C) (I : Type w) (F : I → Subobject X),
    simpleSubquotientClasses (subobjectSum F : C) =
      ⋃ i, simpleSubquotientClasses (F i : C)
```

The family universe `w`, Hom universe `v` and object universe `u` are
independent. Every index type is included, including the empty one.
The imported statement pair and everything it imports remain unchanged.

## Source and scope

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix A.VI.3,
the unnumbered Lemma (iii), printed page 264 / PDF270. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; original file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF269–270 were read completely and PDF270 was visually checked.
The source Grothendieck and canonical local finite type AB6 hypotheses
are introduced at the end of PDF269 and retained in this target.

The public Appendix A discrepancy note concerns other passages.
The supplementary registered `renard-2010-corrections-complements`,
PDF18–19, was read. Its nearby chain correction concerns the preceding
simple-quotient Proposition's Zorn argument; no inspected entry changes
this Lemma. That errata document belongs to a different edition, so this
is a bounded comparison. Its retained file is
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.

Renard first obtains the finite sum case from clause (i), then uses
finite partial sums to reduce to a directed increasing family and applies
AB5 to a simple quotient of a subobject. The proof here follows that
structure. Its final directed-family argument uses a kernel vanishing
lemma in place of the source's explicit `M' ∩ (M'' + M_i)` calculation.
The helper lemmas below are internal derived categorical results
implementing the source argument.

## Least upper bounds and the binary case

`hom_eq_zero_of_subobject_isLUB` states that a morphism from the object
underlying an actual least upper bound is zero if it restricts to zero on
every member. Compose its kernel inclusion into the ambient object.
The restriction hypotheses and the actual kernel universal property make
this kernel subobject an upper bound. Leastness gives a factorization of
the entire least upper bound through the kernel, forcing the morphism
to vanish. No complete lattice or sum indexed by all subobjects is used.

`simpleSubquotientClasses_sup` proves the binary join identity in every
abelian category. Inside `P ⊔ Q`, quotient by the image subobject of the
inclusion of `P`. The inclusion of `Q` followed by this actual cokernel
projection is epi: any subsequent morphism annihilating it also vanishes
on `P`, hence vanishes on their least upper bound, and then vanishes by
cancellation with the cokernel projection. The published clause (i)
inclusion and its mono/epi transport helpers identify all simple classes
with those occurring in `P` or `Q`. The reverse inclusion transports
along the two actual inclusion monomorphisms.

`simpleSubquotientClasses_finset_sup` applies finite induction. The
insertion step uses this binary identity. In the empty step, the bottom
subobject is categorically zero, so the published
`simpleSubquotientEmpty` theorem gives the empty class set. Its source
antecedents are supplied unchanged.

## Directed families and arbitrary sums

`simpleSubquotientClasses_directed_isLUB` takes a nonempty directed
`w`-indexed family and its actual least upper bound `U`. A simple
subquotient of `(U : C)` is an actual cokernel of nested subobjects.
Compose its numerator inclusion with `U.arrow` to obtain an ambient
subobject `M` and an actual epimorphism `p : (M : C) ⟶ S` to that simple
cokernel.

Source AB5 says that the intersections `M ⊓ F i` have least upper bound
`M ⊓ U = M`. If all restrictions of `p` to these intersections were
zero, the least-upper-bound vanishing lemma would give `p = 0`.
Epimorphy would then force the identity of `S` to vanish, contradicting
simplicity. Some restriction is therefore nonzero and hence epi because
its target is simple. The same intersection has an actual monomorphism
into `(F i : C)`. The published
`objectClass_mem_simpleSubquotientClasses_of_mono_epi` constructs the
required actual nested-subobject cokernel witness for that member.
The other inclusion transports along `F i ⟶ U`.

For the final theorem, take `T s := s.sup F`, indexed by `Finset I`.
This family is directed by finite union and nonempty because the empty
finset is included, even when `I` is empty. The public construction's
upper-bound laws prove that its least upper bound is precisely
`subobjectSum F`, the image of the actual coproduct map. Apply the
directed-family theorem and replace each partial sum's class set by its
finite identity. Singleton partial sums give the reverse set inclusion.

`Finset I : Type w`, so the only AB5 application has the supplied family
size. There is no indexing by all subobjects, no shrinking premise and no
identification of the three universes. The objects, inclusions, kernels,
cokernels, coproduct image and isomorphism classes are the unchanged
published constructions. The argument adds no finite-type, finite-length,
smallness, well-poweredness, local-smallness, concrete-category, module,
generator or separator hypothesis.

The module imports the accepted clause (i) proof
`Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`
(Worker 695) and clause (ii) proof
`Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty` (Worker 595).
Those published proofs are reused by Lean name. Their ownership is
preserved. This module supplies only clause (iii); the aggregate identity
target and the later supported-sum and decomposition results remain
separate obligations.

The approved Lean service compiled this module with zero errors and warnings
and completed a Lake build with inspection. It reports independent level
parameters `w`, `v`, `u` and only `propext`, `Classical.choice` and
`Quot.sound`. A private signature module assigned the complete unapplied
constant directly to both the named proposition and its expanded telescope;
both checks passed without adapting arguments. These are development checks,
separate from the staged candidate's machine validation, independent semantic
review and publication.
