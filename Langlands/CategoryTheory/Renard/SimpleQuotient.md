# Renard A.VI.3: simple quotients and simple subquotients

Authors: Worker 6 (proof draft) and Worker 961 (independent check and
submission).

This proof unit proves the unchanged public
`Langlands.Renard.SimpleQuotientPropositionStatement` and its two component
statements in an arbitrary abelian category. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix A.VI.3, printed pages 263–264 / PDF269–270,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The supplementary registered `renard-2010-corrections-complements`, PDF18–19,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
corrects the older sequence argument to a chain; the governing 2026 passage
already uses a chain. The public Appendix A discrepancy note records other
passages. The registered author-page snapshot `renard-author-page-2026-10-26`
links the 2026 edition and only the 2010 errata; no separate 2026 errata
is listed there.

For a nonzero finite-type object, `exists_simple_cokernel_of_finiteType`
applies Mathlib's Zorn lemma to the set of all proper actual subobjects.
The empty chain is bounded by the bottom subobject, which is proper because
the object is nonzero. For a nonempty chain, the published finite-type
predicate supplies a least upper bound and rules out its being top.
Maximality then gives a cover of the maximal proper subobject by top.
The published `simple_cokernel_ofLE_iff_covBy` gives simplicity of the
cokernel of its inclusion into the top subobject. Composing that inclusion
with the top subobject's isomorphism to the ambient object gives its actual
subobject arrow. `cokernelIsoOfEq` and `cokernelCompIsIso` transport simplicity
to the required actual cokernel of that arrow. This stronger helper does
not require the category-wide Grothendieck or AB6 assumptions.

For the second clause, `isFiniteTypeObject_of_isZero` proves that every
zero object is finite type: its subobject order is a subsingleton, so all
subsets have a least upper bound and no nonempty set of proper subobjects
exists. Thus a nonfinite-type object is nonzero.
`exists_nonzero_finiteType_subobject` uses canonical source AB6 to obtain
a nonzero finite-type subobject `B`. If all finite-type subobjects were
zero, their arrows would be zero and hence each would be bottom. Bottom
would then bound the canonical AB6 cover, forcing top below bottom in the
nontrivial subobject lattice of the nonzero object. This supplies explicitly
the witness omitted in the source's brief second-clause argument.

Apply the first helper within the underlying object of `B` to obtain a
proper subobject `P` with simple cokernel. The witness in the ambient object
is the actual subobject `A = Subobject.mk (P.arrow ≫ B.arrow)`.
`mk_lt_mk_of_comm` proves `A < B` because `P.arrow` is not an isomorphism.
The chosen representative isomorphism
`e : (A : C) ≅ (P : C)` identifies the actual inclusion `A → B` with
`e.hom ≫ P.arrow`, as shown by canceling the monomorphism `B.arrow`.
`cokernelIsoOfEq` followed by `cokernelEpiComp` gives the explicit isomorphism
from the required actual cokernel of `Subobject.ofLE A B hAB.le` to
`cokernel P.arrow`. `Simple.of_iso` transports simplicity along it.

The public component proofs `finiteTypeSimpleQuotient` and
`nonFiniteTypeSimpleSubquotient`, and their conjunction
`simpleQuotientProposition`, retain both source antecedents inside the
unchanged targets. Their explicit outer telescope is `(C : Type u)` with
`[Category.{v} C] [Abelian C]`, with independent universes `w`, `v`, `u`.
Zorn and canonical AB6 use the entire actual subobject type in
`Type (max u v)`; no bound by the separate family universe `w` is needed.
There is no additional generator, finite length, module, concreteness,
well-poweredness, local-smallness or universe-identification assumption.

The zero-object and AB6 witness lemmas and explicit quotient transports
are internal elaborations of the cited source proof, rather than additional
source assertions. The accepted statement pair and all of its imported
Lean/Markdown closure remain unchanged. Compilation and private draft
sharing provide no independent proof acceptance or publication.

The approved Lean service compiled the proof module and a separate private
probe with a Lake build and no errors or warnings. The probe assigns each
of the three public proof constants, unapplied, to the complete telescope
of its published target and prints their independent universe parameters.
All six new theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`. The diagnostic probe is excluded from this shareable proof unit.
Worker 961 repeated these checks independently with the unchanged Lean file
(SHA256 `248e494c...7329`): check `e47bbf93-c7b0-4b76-87e0-a390a44b8fd2`
reports no errors or warnings, level parameters `w, v, u` and the same
three axioms. A private probe, check `c63ebe27-275b-43b9-87f0-b7547e2eed3b`,
elaborates each public proof against its full target telescope. It also
instantiates the aggregate at distinct universes, `{0, 1, 2}` and
`{3, 1, 2}`, on `ModuleCat.{1} ℤ`.
These development checks do not replace the independent semantic review
or the final staged proof's exact-target validation and publication.
