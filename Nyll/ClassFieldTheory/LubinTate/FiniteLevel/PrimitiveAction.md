# The Lubin–Tate action on primitive division points

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with valuation ring `O_F`, `π` a uniformizer, and `λ` the chosen primitive point of the standard Lubin–Tate level `n`, an element of the complete valuation ring `O_n` of that level. The endomorphisms `[a]` of the standard Lubin–Tate formal module are power series, evaluated at `λ` in `O_n`. The file shows that units act on `λ` through roots of the primitive polynomial, and that the action is faithful exactly modulo `U^(n+1)`.

## Main definitions and results

- `SameUniformizer.standardLubinTateEndomorphism_uniformizer`: `[π]` is the standard series `X^q + πX`, `q` the cardinality of the residue field of `F`; hence, for `x` in `O_n` topologically nilpotent (`hx : PowerSeries.HasEval x`), `[π^r](x)` is the `r`-th polynomial iterate evaluated at `x` (`standardLubinTateEndomorphismEvalAt_uniformizer_pow`).
- `standardLubinTateFormalAdd`: addition of the standard formal group, evaluated on `O_n`; for such `x`, `[a + b](x)` is the formal sum of `[a](x)` and `[b](x)` (`standardLubinTateEndomorphismEvalAt_add`, `standardLubinTateEndomorphismValue_add`).
- `standardLubinTateEndomorphismEvalAt_zero_point` and `standardLubinTateEndomorphismEvalAt_unit_injective`: every `[a]` fixes `0`, and a unit `[u]` is injective on topologically nilpotent elements.
- `standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow`: `[a](λ) = 0` iff `a ∈ m^(n+1)`; the annihilator of `λ` is exactly `m^(n+1)`.
- `standardLubinTatePrimitivePointIntegerAction hπ n u`: the element `[u](λ)` of `O_n` for a unit `u`; `[1](λ) = λ` and `[uw](λ) = [u]([w](λ))`.
- `standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup`: `[u](λ) = λ` iff `u ∈ U^(n+1)`; more generally `[u](λ) = [w](λ)` iff `u/w ∈ U^(n+1)`.
- `standardLubinTatePrimitiveLevelAction`, `standardLubinTatePrimitiveRootAction`: `[u](λ)` viewed in the level field and in the separable closure of `K`, with the same congruence criterion (`standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup`).
- `standardLubinTatePrimitiveRootAction_isRoot`: `[u](λ)` is a root of the primitive polynomial of level `n` over `K`.

## Proof

For the annihilator, write `a = u·π^r`; `[a](λ) = [u]([π^r](λ))` vanishes iff `[π^r](λ) = f^(r)(λ)` does, which by the earlier iterate computations happens exactly for `r ≥ n + 1`. The fixed-point criterion applies this to `u − 1`, using additivity through the formal group law. For the root statement, `[u](λ)` is killed by `f^(n+1)` but not by `f^(n)`, and `f^(n+1) = f^(n)·Q_n`.

## Points to watch

- Evaluation uses the same local topologies as the file on completed evaluation: discrete on `O_F`, maximal-ideal-adic on `O_n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveAction.lean`: the Lean file is the source byte for byte (SHA-256 `55acc154d90358f39ecf1993d375278959c95413a7074700544b4406a2243b18`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
