# Left invariance of intertwining integrals under the target group

Module `Langlands.Global.CuspidalTestExpansion.IntertwiningInvariance`
(namespace `Langlands.Global.AdelicGroupPoints`).

## Statement

`IsIwasawaCompact.intertwiningIntegral_adelicPoints_mul`: let `p : P → G` be a closed subgroup
with an Iwasawa subgroup `K`, `iU : U → P` with `U` unipotent, `j : V → G` a closed subgroup
whose rational quotient `V(F) \ V(𝔸)` is compact, and `w` a rational point. If `φ` is left
invariant under `U(𝔸)`, then for every `u ∈ V(𝔸)` and `y`,
`hK.intertwiningIntegral iU j w φ λ (u y) = hK.intertwiningIntegral iU j w φ λ y`.

## Proof

The integral runs over `(V(F) ∩ w U(𝔸) w⁻¹) \ V(𝔸)` with the quotient of the normalized Haar
measure of `V(𝔸)`. That Haar measure is right invariant because `V(F) \ V(𝔸)` is compact
(`haar_isMulRightInvariant_of_compactRationalQuotient`), so right translation by `u` on the
discrete quotient is measure preserving (`measurePreserving_rightTranslate_discrete`). The
integrand at `u y` is the integrand at `y` composed with this translation
(`intertwiningIntegrand_mk`), and `MeasurePreserving.integral_comp` concludes.
