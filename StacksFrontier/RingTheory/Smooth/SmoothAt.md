# Smoothness at a prime from flatness and a smooth fibre

Module `StacksFrontier.RingTheory.Smooth.SmoothAt`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves a local criterion for smoothness of a map of commutative rings using a smooth fibre. Smoothness at a prime q of S is spelled out as the existence of g outside q for which the R-algebra `Localization.Away g` is smooth.

## Results

- `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber` starts with primes p of R and Q of `p.Fiber S`, and a prime q of S pinned by the comap equality `hq`. If `Localization.AtPrime q` is flat over R, the fibre is smooth at Q in Mathlib’s sense, and `hfp` gives finite presentation on some basic open containing q, then a basic open containing q is smooth over R.
- The localization lemmas identify the prime localization before and after inverting an element outside the prime.

## Proof

The local fibre is identified with the base change of the prime localization to κ(p) over the local ring at p. The formal smoothness criterion for flat local algebras applies on the finitely presented chart, and clearing denominators produces a basic open of Spec S.

## Scope

Mathlib’s `Algebra.IsSmoothAt` means formal smoothness of the prime localization. It can hold at every prime even when no `Localization.Away g` is smooth, as for a polynomial algebra in infinitely many variables over a field. The fibre hypothesis uses `Algebra.IsSmoothAt`, and the conclusion gives actual smoothness on a basic open. Flatness over R is equivalent here to flatness over the local ring at p.

The module docstrings of the first and last sections describe results that are not in the file: that a ring map is smooth exactly when it is smooth at every prime of the target (Stacks 00TC), and the openness of the locus of Definition 00TB with its comparison to Mathlib’s smooth locus. Those sections declare nothing.

## References

Tag 00TF for flatness with a smooth fibre, and Tag 00TB for the smoothness at a prime spelled out in its conclusion. Related references are EGA 0 19.7.1, SGA 1 II 2.1 and SGA 3 VIB 3.10.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00TF](https://stacks.math.columbia.edu/tag/00TF) | `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber` | Smoothness at `q` in the conclusion is spelled out as Definition 00TB, `∃ g ∉ q` with `Localization.Away g` smooth over `R`, while smoothness of the fibre at `Q` is Mathlib's `Algebra.IsSmoothAt`; the two notions agree under hypothesis (1), so this is the weakest hypothesis with the strongest conclusion. The fibre is `Ideal.Fiber` and `Q` is pinned as the prime corresponding to `q` by `hq`, the inverse of `PrimeSpectrum.preimageEquivFiber`. Flatness of `R_p → S_q` is stated over `R`, which for the `R_p`-algebra `S_q` is the same condition (`Module.flat_iff_of_isLocalization`). This is the full generality of the tag; upstream's `Algebra.IsSmoothAt.of_formallySmooth_fiber` is the case of all three hypotheses imposed globally. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.7.1 | `formallySmooth_of_flat_of_formallySmooth_residueField_tensor` | b ⇒ a |
| SGA | 1 II 2.1 | `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber` | (a) + (b) ⇒ smooth |
| SGA | 3 VIB 3.10 | `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Smooth/SmoothAt.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 8 are kept. The 9 left out are not needed by the results for which the extract is made: `Algebra.SmoothAt`, `Algebra.isOpen_setOf_smoothAt`, `Algebra.isSmoothAt_of_smoothAt`, `Algebra.setOf_smoothAt_eq_smoothLocus`, `Algebra.smoothAt_iff`, `Algebra.smoothAt_iff_isSmoothAt`, `Algebra.smooth_iff_forall_exists_notMem_smooth`, `Stacks.Smooth.PointwiseCriterion.solution`, `Stacks.Smooth.PointwiseCriterion.span_eq_top_iff_forall_isMaximal_exists_notMem`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
