# The canonical elementary tower of an infinite APF extension

Module `FontaineWintenberger.APF.Tower.Canonical`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L` an infinite APF intermediate field of its separable closure. Following Wintenberger §1.4.1, the file enumerates the positive upper breaks of `L/K`, attaches to each a finite subfield, and shows that these fields form a strictly increasing tower with union `L` whose successive steps are elementary. It then expresses the first ramification bound and the strictness constant of `L/K` through this tower.

## Definitions

- `apfUpperBreak K L : ℕ → ℝ`: the increasing enumeration of the positive upper breaks, chosen from `exists_apfUpperBreaks`.
- `apfElementaryStage K L n`: the finite field `apfFiniteStage K L (apfUpperBreak K L n)`; its fixing subgroup is the APF product at the `n`-th break.
- `apfElementaryLevel K L n`: the lower-numbered break `apfPsi K L (apfUpperBreak K L n)`.

## Results

- The breaks are positive, strictly increasing, tend to infinity, and are exactly the `IsAPFUpperBreak` points (`isAPFUpperBreak_iff_mem_range`); the APF product is constant on `(b n, b (n+1)]` and on `(0, b 0]`.
- `strictMono_apfElementaryStage`, `exists_le_apfElementaryStage`, `iSup_apfElementaryStage`: the tower is strictly increasing, every finite subextension of `L` lies in a stage, and the union is `L`.
- The levels are positive, strictly increasing and tend to infinity; `apfElementaryLevel_eq` computes them with the Herbrand function of the finite stage.
- `isElementaryStep_apfElementaryStage`: stage `n + 1` over stage `n` is an elementary step of level `apfElementaryLevel K L n`.
- `apfSubgroup_eq_top_iff_le_first_upperBreak` and `apfRamificationBound_eq_apfElementaryLevel`: if `0 < apfRamificationBound K L`, the APF product at `u ≥ -1` is the whole group exactly for `u ≤ b 0`, and the bound equals the level of index `0` (Wintenberger's `i(L/K) = i₁`).
- `apfStrictnessConstant_eq_iInf_apfElementaryLevel`: under the same hypothesis, the strictness constant is the infimum over `n` of level `n` divided by the degree over `K` of stage `n + 1`.
- `apfRamificationBound_over_apfElementaryStage`: the ramification bound of `L` over stage `n`, with the spectral norm on the stage, equals level `n`.
- `isStrictlyAPF_iff_apfElementaryLevel_div_finrank_of_ramificationBound_pos`: for a positive bound, strict APF is equivalent to a uniform positive lower bound on those quotients.
- For `IsPerfectResidueLocalField K`: `apfElementaryStage_zero` identifies stage `0` with `apfTameStage K L`, and `apfElementaryStage_finrank_eq_prime_pow` says each step has degree a power of the residue characteristic.

## Points to watch

- Indexing starts at zero: `apfElementaryStage n` is Wintenberger's `Kₙ₊₁` and `apfElementaryLevel n` his `iₙ₊₁`. The unramified stage is `apfFiniteStage K L 0`.
- Infiniteness is carried as an instance `Fact (¬ Module.Finite K L)`.
- The formulas for the bound and the constant assume `0 < apfRamificationBound K L`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Canonical.lean` (SHA-256 of the source file `6be66a1dc5e5399537176e94a2a14b1dbf4302be8226249afb7da615c2b0aa42`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
