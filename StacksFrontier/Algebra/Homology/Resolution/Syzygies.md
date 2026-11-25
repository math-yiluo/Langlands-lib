# Syzygies of a resolution

Module `StacksFrontier.Algebra.Homology.Resolution.Syzygies`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative ring `R` and an `R`-module `M`, the file defines the syzygies of a resolution datum `P : FreeResolutionData R M`, that is of an augmented sequence `⋯ → F 1 → F 0 → M → 0` of `R`-linear maps, and proves that, when `P` is exact, they fit into short exact sequences `0 → K (n+1) → F n → K n → 0`.

## Definitions and results

- `FreeResolutionData.delta n`: the augmented differentials, `ε : F 0 → M` for `n = 0` and `d (n-1) : F n → F (n-1)` after that, with targets `target n`.
- `IsComplex.delta_comp_delta` and `IsExact.range_delta_succ` restate the complex and exactness conditions along `delta`; `IsExact.isComplex`: an exact datum is a complex.
- `FreeResolutionData.syzygy n`: `M` itself for `n = 0` and the submodule `ker (delta (n-1))` of `F (n-1)` after that, with the module structures carried along.
- `syzygyIncl n : K (n+1) → F n`, the inclusion, and `syzygyProj hc n : F n → K n`, the augmentation for `n = 0` and the corestriction of `delta n` after that; the latter needs a proof `hc` that the datum is a complex.
- `injective_syzygyIncl` and `exact_syzygy` (exactness in the middle) hold for any complex; `surjective_syzygyProj` uses exactness.
- `finite_syzygy`: over a noetherian ring, if `M` is finite and every `F n` is finite, every syzygy is finite.

## Watch for

- The syzygies are defined by a case split on `n`, not by recursion; `syzygy 0` is literally `M`, so statements about `M` apply to it without transport.
- Short exactness is stated as three separate properties of linear maps (`Function.Injective`, `Function.Exact`, `Function.Surjective`), not as a short exact sequence in `ModuleCat R`.
- `finite_syzygy` does not use exactness, and freeness of the `F n` plays no role anywhere in the file.
- The module docstring also mentions a statement bundling the three properties, which the file does not contain.

## References

The file names Tags 00LP and 00RC.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/Resolution/Syzygies.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 22 declarations of the source file 20 are kept. The 2 left out are not needed by the results for which the extract is made: `FreeResolutionData.shortExact_syzygy`, `FreeResolutionData.syzygy_zero`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
