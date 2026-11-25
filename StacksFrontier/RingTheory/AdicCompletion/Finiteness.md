# Finite generation from reduction modulo an ideal

Module `StacksFrontier.RingTheory.AdicCompletion.Finiteness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over an adically precomplete commutative ring, a separated module is finitely generated if its reduction modulo the defining ideal is finitely generated.

`Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top` proves this for an ideal I of R and an R-module M, with the proof packaged as `Stacks.AdicCompletion.SeparatedFiniteness.solution`. The assumptions are `IsPrecomplete I R`, zero intersection of the submodules IⁿM, and finiteness of M/IM as an R/I-module. The conclusion is `Module.Finite R M`. For any submodule N with M/N finite over R, the helper `Stacks.AdicCompletion.SeparatedFiniteness.exists_surjective_mkQ_comp` lifts a surjection onto M/N to a map from a finite free module into M.

The proof uses that lift for N = IM, after viewing the finite reduction as an R-module. Finite products preserve precompleteness, so `surjective_of_mkQ_comp_surjective` upgrades surjectivity modulo I to surjectivity onto the separated target M.

The base-ring hypothesis is weaker than the completeness assumption in the Stacks statement. It only requires the map from R to its completion to be surjective. The separatedness hypothesis is on M.

The finiteness result is Tag 031D. The alternative proof in the Stacks Project uses the completeness result of Tag 031B and the surjectivity on completions of Tag 0315. The comments refer to Tag 00ML, Tag 05CG, and Tag 0471 for the quotient-module convention.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [031D](https://stacks.math.columbia.edu/tag/031D) | `Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/Finiteness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
