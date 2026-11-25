# Relations and tensor vanishing in directed systems

Module `StacksFrontier.RingTheory.Flat.ColimitTrivialRelation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For rings Aᵢ and modules Nᵢ with compatible transitions and colimits R and M, the file shows how finite relations and tensor identities over R can be witnessed at a stage of the system.

## Main results

- `Module.exists_hom_isTrivialRelation_of_isColimit` shows that if M is R-flat, each finite relation at a stage i becomes trivial at some j ≥ i. In Mathlib's `Module.IsTrivialRelation`, the module elements are combinations of finitely many vectors, with coefficient columns giving syzygies on the original ring coefficients.
- `Module.Flat.of_isColimit_of_forall_exists_ge_flat` shows that if every stage has a later stage j with Nⱼ flat over Aⱼ, then M is R-flat.
- `Ideal.exists_tmul_vanishing_certificate` and `Ideal.sum_tmul_eq_zero_of_vanishing_certificate` express vanishing of a finite tensor sum in I ⊗ N over a commutative ring by finite equations. The witnesses allow extra elements of I. Using these witnesses, `Ideal.exists_hom_tmul_eq_zero_of_isColimit` shows that a sum represented at i which vanishes in I ⊗ M over R also vanishes in Iⱼ ⊗ Nⱼ at some j ≥ i, where Iⱼ is the inverse image of I.
- `Module.IsTrivialRelation.sum_tmul_eq_zero` shows that a trivial relation with coefficients aₖ in an ideal I gives ∑ₖ aₖ ⊗ vₖ = 0 in I ⊗ N. `TensorProduct.exists_sum_tmul_of_span_eq` writes every element of I ⊗ N as ∑ₖ aₖ ⊗ vₖ for a given finite generating family aₖ of I.
- `Module.sum_tmul_eq_zero_of_mem_ker_rTensor` and its primed variant show that a comparison map with prescribed values on the tensors aₖ ⊗ m for chosen generators aₖ of I (`hΦ`) kills the kernel of the map induced by I ⊆ R. Given a finite generating family of I and a finite family spanning its module-valued syzygies, the unprimed lemma assumes `htriv` for their images and the primed lemma assumes tensor vanishing `hvanish`. Helper lemmas, `Module.IsTrivialRelation.mapOfSystem`, its primed variant and `Ideal.tmul_eq_zero_of_mapOfSystem`, preserve triviality and tensor vanishing along transitions.

The flatness arguments use the equational criterion and lift finite families of witnesses and equalities to a common stage. The vanishing certificate first captures the tensor identity in a finitely generated submodule of I, whose generators supply the extra witnesses.

## Scope

The stage results use a nonempty directed preorder, with the index, rings and modules in one universe. The hypotheses `hsmul` and `hν` give compatibility of the module actions with the transitions and colimit maps. Tensor-vanishing descent applies to arbitrary modules in these systems and uses the entire inverse image ideal Iⱼ. The module docstring also lists a lemma on scaling the vectors of a trivial relation, which is not in the file.

The comments cite Tag 00HK for the equational criterion, Tag 00MO for the comparison map, and Tag 00R6 and Tag 0471 for applications of the stage arguments.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/ColimitTrivialRelation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 16 are kept. The 1 left out are not needed by the results for which the extract is made: `Module.IsTrivialRelation.const_smul`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
