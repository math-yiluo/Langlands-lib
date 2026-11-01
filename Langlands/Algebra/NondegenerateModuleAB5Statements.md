# Source AB5 for original nondegenerate modules

Authors: Worker 6 and Worker 695. Worker 6 authored the shared statement
draft. Worker 695 checked the original passages and public dependencies,
finalized the explanation, and checked the complete universe interfaces.

This statement unit records the AB5 assertion of Renard I.6 for the published
actual category `NondegenerateModuleCat A`, with its original additive
intertwiners and named abelian structure
`NondegenerateModuleCat.abelian A hA`. It supplies proposition definitions
only, with no proof of the new assertions.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.6 Proposition and proof,
printed pp.27–28 / PDF pp.33–34, especially the displayed AB5 formula on
printed p.28 / PDF p.34. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 695 read both pages in full and visually checked PDF p.34.
Appendix A.VI.2,
printed p.263 / PDF p.269, fixes the source's AB5 convention, represented by
the published `Langlands.Renard.SourceAB5` predicate. Worker 695 read and
visually checked that page as well and recomputed the original PDF's hash.
The existing predicate's paired Markdown documents the terminology.

No separate project errata note for the registered 2026 source was present
at authoring. The supplementary author correction list for the 2010
edition, registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was rechecked at PDF pp.1–2 and 18–19; none of those entries changes the
AB5 assertion or convention used here. This limited check is not a claim
to have read every correction or found every possible later erratum.
The 2026 original remains the governing edition.

The book assumes an idempotented complex algebra. These targets range over
an arbitrary nonunital idempotented ring. This is an explicit extension of
the source setting: the directed-union argument in I.6 uses stable additive
subgroups and their actual underlying sets, while finite common local units
prove nondegeneracy of the actual direct sum. Neither step requires complex
coefficients, a unit or finite dimension. The task does not replace the
original action by a unital action as an input.

`DirectedSubobjectDistributivity` says that for every actual object M,
every nonempty directed family F of categorical subobjects, and every
subobject N, a least upper bound U of F exists, and N intersect U is a
least upper bound of the family N intersect F(i). It uses exactly
`Langlands.Renard.DirectedSubobjectSumsDistribute`, hence the existing
categorical factorization order and pullback intersection on
`CategoryTheory.Subobject M`. It does not introduce a new subobject order
or assume a complete lattice instance. Both sums in the source formula
are asserted to exist. Directedness expresses a common upper bound within
the family for every pair; nonemptiness follows the source's filtered-system
convention. The family universe `uI` is independent of the coefficient
universe `uA` and the fixed module carrier universe `uM`. This first law
asserts no existence of coproducts indexed above the carrier universe.

`SourceAB5Statement` asserts the full published `Langlands.Renard.SourceAB5`
condition, including existence of `uI`-indexed coproducts, for
`NondegenerateModuleCat.{uA,max uI uM} A`. The displayed bound allows the
actual finite-support direct sum to stay in the category. The ring universe
is independent and contributes no carrier bound. Source AB5 here means
cocompleteness in Renard's sense together with the directed-subobject law;
it is not defined to be Mathlib's filtered-colimit exactness class
`CategoryTheory.AB5OfSize`. No comparison theorem between these conventions
is supplied by this unit.

`AB5Assertions` conjoins those two universally quantified targets.
Reflexive unfolding checks pin the first target to both actual least-upper-
bound assertions and pin the second to coproduct existence plus that law.
Closed proposition examples retain arbitrary independent `uA,uI,uM`, both
unequal coefficient/carrier orders and an index universe larger than the
first law's carrier universe, together with all six permutations of the
three distinct levels `0,1,2`.

The actual subobject comparison, the directed-union and coproduct proofs,
source AB6 (local finite type, as distinguished in I.6 footnote 3), and
filtered-colimit exactness remain separate obligations. This pair does not
assert completion of I.6 or the whole-book program.
