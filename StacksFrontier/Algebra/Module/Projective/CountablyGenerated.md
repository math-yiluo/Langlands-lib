# Projective modules and countable generation

Module `StacksFrontier.Algebra.Module.Projective.CountablyGenerated`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on projectivity and countable generation: freeness of all projective modules over a ring reduces to the countably generated ones.

## Main results

- `Module.forall_free_of_projective_iff_forall_free_of_projective_of_countable_span` (Tag 0590), proved as `Module.CountableSpanFree.forall_free_iff`: for any ring `R` (not necessarily commutative), every projective `R`-module is free if and only if every projective `R`-module with a countable spanning set is free. Both sides quantify over modules in one universe `v`, unrelated to the universe `u` of `R`.

## Proofs

One direction is a weakening of the hypothesis. For the other, Kaplansky's decomposition (Tag 058Y, from another file) writes a projective module as an internal direct sum of countably generated projective submodules, free by hypothesis; a private lemma shows that an independent set of free submodules with supremum `⊤` makes the module free, and another turns a submodule spanned by a countable subset of `M` into a module with a countable spanning set of its own.

## Watch for

- Countable generation is written inline, as `∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤`, not as a predicate.
- The module docstrings also describe Tags 05A0 and 05A1 (a direct sum of countably generated modules that maps universally injectively into a flat Mittag-Leffler module, or into a power series ring over a Noetherian ring, is projective) and name declarations for them. The file holds neither result; their namespaces are empty.

## References

Tag 0590, and Kaplansky, *Projective modules*, Ann. of Math. 68 (1958). The proof rests on Tag 058Y; the comments cite further tags.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0590](https://stacks.math.columbia.edu/tag/0590) | `Module.forall_free_of_projective_iff_forall_free_of_projective_of_countable_span` | The equivalence, with countable generation written as a countable spanning set. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Module/Projective/CountablyGenerated.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 4 are kept. The 6 left out are not needed by the results for which the extract is made: `Module.CountableSpanProjective.flat_of_forall_rTensor_injective`, `Module.CountableSpanProjective.lTensor_injective_of_rTensor_injective`, `Module.CountableSpanProjective.projective_of_sSupIndep_countable_span`, `Module.MvPowerSeriesSubmodule.projective_of_mvPowerSeries`, `Module.projective_of_forall_rTensor_injective_mvPowerSeries_of_exists_sSupIndep_countable_span`, `Module.projective_of_forall_rTensor_injective_of_exists_sSupIndep_countable_span`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
