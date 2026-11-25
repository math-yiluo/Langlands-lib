# Finite projective resolutions over a Noetherian ring

Module `StacksFrontier.Algebra.Homology.ProjectiveDimension.FiniteResolution`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a (left) Noetherian ring, not necessarily commutative, `M` a finite `R`-module and `d : ℕ`. The file shows that `M` has projective dimension at most `d` exactly when it has a resolution `0 → P_d → ⋯ → P₀ → M → 0` by finite projective modules.

## Main results

- `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite` (equal to `Stacks.FiniteProjectiveResolution.solution`): for `M : ModuleCat.{v} R` with `Module.Finite R M`, `IsNoetherianRing R` and `Small.{v} R`, `HasProjectiveDimensionLE M d` holds iff there is a left resolution of `M` (the library's `ObjectProperty.LeftResolution`: a chain complex with a quasi-isomorphism to `M` placed in degree `0`) by modules that are projective and finite over `R` whose terms vanish in degrees `> d`.
- Private helpers: splicing a resolution by projectives of a class `Q` onto a short exact sequence `0 → Z → P → Y → 0` with `P` in `Q` (`prepend`); and a finite module as a quotient of a finite free module, without commutativity (`exists_surjective_of_free_of_finite`).

## How it is proved

The backward direction forgets finiteness and applies the library's characterization of projective dimension by resolutions (`hasProjectiveDimensionLE_tfae_leftResolution`). The forward direction is by induction on `d`. One covers `M` by a finite free module `P₀`; the kernel of `P₀ → M` is finite because `R` is Noetherian, and has projective dimension at most `d - 1` by dimension shifting. Its resolution is then spliced onto `P₀`.

## Watch for

- Only the equivalence of the source's condition (6) with the first condition of Tag 0CXC is stated; the other equivalences come from that lemma.
- Projectivity is the categorical `Projective N` in `ModuleCat R`, and "length `d`" means vanishing of the terms above degree `d`.
- `Small.{v} R` is assumed so that finite free covers exist in `ModuleCat.{v} R`.

## References

- Tags 0CXE, 0CXC, 0CXD, 00LP, 00LQ, 00O7, 0A5Q; places in EGA in the table of references below.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CXE](https://stacks.math.columbia.edu/tag/0CXE) | `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite` | Condition (6) is added to Lemma 0CXC by stating its equivalence with item 1 of that lemma's `TFAE`. A resolution `0 → P_d → ⋯ → P₀ → M → 0` by finite projectives is an `ObjectProperty.LeftResolution` for the class of finite projective modules (00LQ), the notion 0CXC, 0CXD and 00O7 use, vanishing in degrees `> d`; stated for a not necessarily commutative ring. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.2.1 | `exists_leftResolution_projective_finite` | One direction |
| EGA | 0 17.2.2 | `exists_leftResolution_projective_finite` |  |
| EGA | 0 17.2.1 | `solution` | partial |
| EGA | 0 17.2.2 | `solution` |  |
| EGA | 0 17.2.2 | `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/ProjectiveDimension/FiniteResolution.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
