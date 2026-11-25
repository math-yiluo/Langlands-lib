# Flat modules in short exact sequences

Module `StacksFrontier.RingTheory.Flat.ShortExact`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a short exact sequence 0 → M′ → M → M″ → 0 of modules over a commutative ring R, given by maps f and g with f injective, g surjective and `Function.Exact f g`, `flat_of_flat_of_flat_quotient` proves that M′ is flat when M and M″ are flat.

The proof tests flatness of M′ on an injective map u : A → B. An element x of the kernel of u ⊗ M′ goes to zero in A ⊗ M, by naturality of the tensor maps (the private `tensor_naturality`) and flatness of M; and A ⊗ M′ → A ⊗ M is injective because M″ is flat, so x = 0.

The module docstring is about the formula IM ∩ JM = (I ∩ J)M for a flat module M (Tag 0BBY), which is not in this file.

## References

Stacks Project, Tag 00HM. EGA IV 2.1.8 and SGA 1 IV 1.1 for short exact sequences. The table of references below gives further EGA and SGA attributions.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00HM](https://stacks.math.columbia.edu/tag/00HM) | `flat_of_flat_of_flat_quotient` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 20.6.21 | `flat_of_flat_of_flat_quotient` | more general |
| EGA | 0 6.1.2 | `flat_of_flat_of_flat_quotient` | M flat implies M' flat |
| EGA | IV 2.1.10 | `flat_of_flat_of_flat_quotient` | Affine case |
| EGA | IV 2.1.8 | `flat_of_flat_of_flat_quotient` | (ii) |
| SGA | 1 IV 1.1 | `flat_of_flat_of_flat_quotient` | (ii) |
| SGA | 4 XVII 4.1.1 | `flat_of_flat_of_flat_quotient` | (i), special case |
| SGA | 6 I 5.1.1 | `flat_of_flat_of_flat_quotient` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/ShortExact.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 2 are kept. The 8 left out are not needed by the results for which the extract is made: `Ideal.map_inf_le_map_mul_of_flat`, `flat_of_flat_of_flat`, `flat_tor_zero`, `ideal_smul_top_inf`, `ideal_smul_top_inf_le`, `phiMap`, `phiMap_rTensor_inclusion`, `tensor_inf_exact`.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 7 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above; the source's 12 others belong to declarations left out.
