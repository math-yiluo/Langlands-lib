# Endomorphisms congruent to the identity modulo 𝔪²

Module `StacksFrontier.RingTheory.AdicCompletion.EndomorphismCongruentToIdentity`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An endomorphism of a commutative Noetherian local ring P, complete for its maximal ideal 𝔪, is surjective if it is the identity modulo 𝔪².

The criterion `surjective_of_residue_surjective_of_cotangent_span` applies to an endomorphism f carrying 𝔪 into itself. It requires that f be surjective modulo 𝔪 and that the classes of f(𝔪) span 𝔪/𝔪² over the residue field. The lemma `surjective_of_sub_id_mem_maximalIdeal_sq` applies it when f(x) − x belongs to 𝔪² for every x in P.

The cotangent spanning condition implies that the extended ideal of 𝔪 along f equals 𝔪. Surjectivity modulo 𝔪 then lifts via `surjective_of_mk_map_comp_surjective`. The congruence gives the identity on both the residue field and the cotangent space.

The module docstring also announces bijectivity, by Tag 06RN; the file proves surjectivity only.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/EndomorphismCongruentToIdentity.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 2 are kept. The 1 left out are not needed by the results for which the extract is made: `bijective_of_sub_id_mem_maximalIdeal_sq`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
