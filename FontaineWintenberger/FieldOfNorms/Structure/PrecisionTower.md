# Deep cofinal towers of finite subfields and their truncated norm maps

Module `FontaineWintenberger.FieldOfNorms.Structure.PrecisionTower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an infinite APF extension of a field `K` with `IsPerfectResidueLocalField K`, and `p` the residue characteristic. Given a finite intermediate field `D`, the file chooses an increasing cofinal sequence of finite subfields `𝔈 n ⊇ D` at which the norm becomes a ring homomorphism modulo `𝔪^(n+2)`, and builds from it a projective system of quotient rings.

## The tower

- `IsAPF.exists_monotone_cofinal_finiteIntermediateFields_ge`: any sequence `A n` of finite intermediate fields of an APF extension lies under a monotone cofinal sequence `E n ⊇ A n`.
- `deepFiniteTowerBound K n = p/(p−1) · (n+2)`, so that `⌈(p−1)/p · deepFiniteTowerBound K n⌉ = n+2` (`ceil_deepFiniteTowerBound`).
- `IsAPF.exists_deep_finiteTower`: there is a monotone cofinal sequence `E n ⊇ D` such that
  - every coordinate at `E n` computes the valuation of the field of norms;
  - `p ∈ 𝔪^(n+2)` in the integer ring of `E n`;
  - for finite `B ⊇ A ⊇ E 0`, the residue inclusion is surjective, `[B : A]` is a power of `p`, and the ramification index equals the degree;
  - for finite `F ⊇ E n`, `deepFiniteTowerBound K n ≤ apfRamificationBound (E n) F`.
- `deepFiniteTower K L D`: a chosen such sequence; its properties are restated as `deepFiniteTower_monotone`, `le_deepFiniteTower`, `deepFiniteTower_cofinal`, `FieldOfNorms.valuation_eq_deepFiniteTower`, `natCast_mem_deepFiniteTower_maximalIdeal_pow`, `deepFiniteTower_wild_tail`, `deepFiniteTower_relativeFirstBound_ge`.

## Quotients and norm maps

- `DeepFiniteTowerQuotient K L D n`: the integer ring of `𝔈 n` modulo `𝔪^(n+2)`, a nontrivial local ring of characteristic `p`.
- `deepFiniteTowerRelativeDegree`: the exponent `d` with `[F : 𝔈 n] = p^d` (`deepFiniteTower_finrank`).
- `deepFiniteTowerNorm`: for finite `F ⊇ 𝔈 n` and `s ≥ n+2`, the surjective ring homomorphism `𝒪_F/𝔪^s → DeepFiniteTowerQuotient n` induced by the norm.
- `deepFiniteTower_integerNorm_add_congruence`: the norm from `F` to `𝔈 n` is additive modulo `𝔪^(n+2)`.
- `deepFiniteTowerTransition n m` (`n ≤ m`): the norm map between quotients. It is surjective, compatible with composition (`deepFiniteTowerTransition_comp`), and the identity for `n = m`.
- `deepFiniteTowerTransition_truncatedAddVal`: the transition sends truncated additive valuation `t` to `min t (n+2)`.

## Proofs

The tower is obtained from composita of `D` with witnesses for four earlier results (a wild tail, stability of the valuation, large relative first bounds, `p` in a high power of the maximal ideal). The norm maps are instances of `FiniteIntermediateField.truncatedNorm`.

## Points to watch

- `deepFiniteTower` is defined by `choose`; only the listed properties are available, and it depends on `D`.
- The precision at stage `n` is `n+2`.
- Infinitude of `L/K` is the hypothesis `Fact (¬ Module.Finite K L)`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/PrecisionTower.lean` (SHA-256 of the source file `36b45aa5277f7f3104db368e85c791abcd1b61f3df5a862e0b59e8b0552826e1`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
