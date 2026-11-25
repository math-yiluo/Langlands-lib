# Reduced closed subschemes and factorization

Module `StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A morphism from a reduced scheme factors through a closed subscheme exactly when its set-theoretic image lies in the support of that subscheme.

- `Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support`: for a reduced scheme Y, an ideal sheaf I on X and f : Y ⟶ X, f factors through the closed subscheme of I exactly when its image lies in `I.support`. Here `I.support` is the underlying closed set of the closed subscheme of I.
- `Scheme.existsUnique_lift_nilradical_subschemeι` gives unique factorization from a reduced scheme through the target’s reduction, the closed subscheme of `X.nilradical`.

The image condition puts I inside the map’s kernel ideal sheaf, so the closed immersion lifts the map, and monicity of the reduction immersion gives uniqueness.

Both results are Tag 0356. The module docstring also announces a uniqueness theorem for the reduced structure on a closed subset (Tag 01J3), which the file does not contain. References include EGA I 4.1.8, EGA I 5.1.5, EGA I 5.2.2, EGA I 10.8.1, EGA III 5.3.5, SGA 3 VIB 7.1 and SGA 3 VIB 7.3.0.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0356](https://stacks.math.columbia.edu/tag/0356) | `exists_lift_subschemeι_iff_range_subset_support` | factorization criterion |
| [0356](https://stacks.math.columbia.edu/tag/0356) | `Scheme.existsUnique_lift_nilradical_subschemeι` | factorization through the reduction |
| [01J3](https://stacks.math.columbia.edu/tag/01J3) | `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` | canonical construction |
| [01J3](https://stacks.math.columbia.edu/tag/01J3) | `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` | underlying closed subset |
| [01J3](https://stacks.math.columbia.edu/tag/01J3) | `AlgebraicGeometry.Scheme.IdealSheafData.stacks_isReduced_subscheme_vanishingIdeal` | reducedness |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 5.2.2 | `exists_lift_subschemeι_iff_range_subset_support` | more general |
| SGA | 3 VIB 7.3.0 | `exists_lift_subschemeι_iff_range_subset_support` | factorization criterion |
| SGA | 3 VIB 7.1 | `exists_lift_subschemeι_iff_range_subset_support` | partial |
| EGA | I 5.1.5 | `Scheme.existsUnique_lift_nilradical_subschemeι` | reduced source factors |
| EGA | I 4.1.8 | `Scheme.existsUnique_lift_nilradical_subschemeι` | special case |
| EGA | I 10.8.1 | `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` |  |
| EGA | III 5.3.5 | `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` |  |
| EGA | I 10.8.1 | `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` | more general |
| EGA | III 5.3.5 | `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/ReducedClosedSubscheme.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 2 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 9 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
