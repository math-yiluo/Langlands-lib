# Free resolutions and Serre’s regularity criterion

Module `StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a regular local ring, depth bounds the length of finite free resolutions. Conversely, finite projective dimension of the residue field detects regularity of a Noetherian local ring.

`IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE` assumes that R is regular local and has dimension at most d. For a finite R-module M of depth at least e at the maximal ideal, it gives a resolution by finite free modules vanishing in degrees above d − e. It also bounds the projective dimension of every R-module by d.

`isRegularLocalRing_tfae` gives five equivalent conditions for a Noetherian local ring R with maximal ideal 𝔪 and residue field κ. They are finite projective dimension of κ, finite global dimension of R, regularity of R, equality of global and Krull dimensions, and equality of global dimension and the dimension of 𝔪/𝔪² over κ.

The resolution proof uses Cohen–Macaulayness of R to reach a maximal Cohen–Macaulay syzygy, which is free over a regular local ring, and extends the projective dimension bound from finite modules to all modules. For Serre’s criterion, the finite projective dimension of κ lies between the embedding dimension and the Krull dimension, and Krull’s height theorem supplies the reverse inequality.

The resolution theorem uses `Module.stacksDepth` and allows the zero module, whose depth is ⊤. The degree bound uses truncated subtraction in ℕ. Both theorems quantify over the module category in the universe of R. Global dimension is expressed as the supremum of projective dimensions in `WithBot ℕ∞`, with finiteness expressed by `≠ ⊤`.

Stacks Project, Tag 00O7 and Tag 00OC, with Tag 00NG, Tag 00NT, Tag 065T, Tag 00OA, and Tag 00OB for the arguments. EGA 0 16.2.6, 16.4.5, 17.3.1 and 17.3.4, SGA 2 IV 5.3, and SGA 6 IX 1.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00O7](https://stacks.math.columbia.edu/tag/00O7) | `solution` | Stated with `ringKrullDim R ≤ d` and `e ≤ depth_𝔪(M)`; see the module docstring of the statement file. |
| [00O7](https://stacks.math.columbia.edu/tag/00O7) | `IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE` | Stated with `ringKrullDim R ≤ d` and `e ≤ depth_𝔪(M)`; the length `d - e` of the resolution is the vanishing of its terms in degrees `> d - e`, and `R` having global dimension `≤ d` is `∀ M, HasProjectiveDimensionLE M d`. See the module docstring. |
| [00OC](https://stacks.math.columbia.edu/tag/00OC) | `isRegularLocalRing_tfae` | Global dimension is the supremum of the projective dimensions of all `R`-modules (Mathlib has no name for it) and \"finite\" is `≠ ⊤`; `dim_κ 𝔪/𝔪²` is the `finrank` of `IsLocalRing.CotangentSpace R` over `IsLocalRing.ResidueField R`. The source's two \"moreover\" equalities are items (4) and (5) of the list, each of which implies the other three. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.4.5 | `exists_isRegular_length_eq_depth` | partial |
| EGA | 0 17.3.4 | `solution` | dim.proj ≤ n - prof |
| SGA | 2 IV 5.3 | `solution` | partial |
| SGA | 6 IX 1.5 | `solution` | partial |
| EGA | 0 17.3.4 | `IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE` | dim.proj ≤ n - prof |
| EGA | 0 17.3.1 | `IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE` | Sufficiency, partial |
| SGA | 2 IV 5.3 | `IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE` | partial |
| SGA | 6 IX 1.5 | `IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE` | partial |
| EGA | 0 16.2.6 | `ringKrullDim_le_finrank_cotangentSpace` |  |
| EGA | 0 17.3.1 | `isRegularLocalRing_of_projectiveDimension_residueField_ne_top` | Necessity |
| SGA | 6 IX 1.5 | `isRegularLocalRing_of_projectiveDimension_residueField_ne_top` | partial |
| EGA | 0 17.3.1 | `isRegularLocalRing_tfae` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularLocalRing/GlobalDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 12 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
