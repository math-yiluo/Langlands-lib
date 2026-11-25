# Krasner's lemma and descent from completion

Module `StacksFrontier.RingTheory.Krasner`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a one-dimensional complete Noetherian local domain, sufficiently small changes to the coefficients of a polynomial preserve the existence of a root near a given root with nonzero derivative. The file uses this approximation to descend finite separable extensions from the fraction field of a completion.

For a Noetherian domain of this kind with maximal ideal m, `krasner_lemma` gives, for each c, an n such that every perturbation Q with coefficients in mⁿ makes P + Q have a root β with β − α ∈ mᶜ, provided P(α) = 0 and P′(α) ≠ 0. The derivative need only be nonzero. `krasner_lemma_of_forall_exists_maximalIdeal_pow_le` replaces Noetherianity with `hpow`, which requires every nonzero u ∈ m to generate an ideal containing a power of m.

`Krasner.exists_finite_separable_extension_tensorProduct_equiv` starts with a Noetherian local ring A whose maximal-ideal-adic completion is a one-dimensional domain. For the fraction fields K of A and K̂ of its completion, every finite separable extension M of K̂ is isomorphic as a K̂-algebra to the scalar extension from K to K̂ of a finite separable intermediate field L of an algebraic closure of K.

`IsLocalRing.exists_root_sub_mem_span_singleton_pow` uses a Newton iteration with a correction obtained by dividing out a fixed power of a nonzero π ∈ m. Adic completeness gives the limit and separatedness makes it a root. The descent proof approximates the monic equation of an integral primitive element by a polynomial over A and uses Nakayama's lemma to retain generation after perturbation.

The formulation of Tag 09EI assumes Noetherianity in addition to the conditions in the Stacks definition of a complete local ring, Tag 0324. This supplies the power containment required by `hpow`. A comment of the file and the docstring of `krasner_lemma` cite an equivalence between that containment and the perturbation conclusion; the equivalence is not in the file.

The descent theorem is Tag 09EJ. The dimension-one step for integral extensions is a special case of EGA 0 16.1.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EI](https://stacks.math.columbia.edu/tag/09EI) | `krasner_lemma` |  |
| [09EJ](https://stacks.math.columbia.edu/tag/09EJ) | `exists_finite_separable_extension_tensorProduct_equiv` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.1.5 | `ringKrullDim_eq_one_of_isIntegral` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Krasner.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 28 declarations of the source file 21 are kept. The 7 left out are not needed by the results for which the extract is made: `Krasner.exists_complete_integral_primitive_order`, `Krasner.exists_finite_integral_primitive_order`, `Krasner.exists_integral_primitive_element`, `Krasner.exists_ne_zero_mul_mem_adjoin`, `Krasner.isFractionRing_adjoin`, `exists_maximalIdeal_pow_le_span_singleton_of_krasner`, `krasner_iff_forall_exists_maximalIdeal_pow_le_span_singleton`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
