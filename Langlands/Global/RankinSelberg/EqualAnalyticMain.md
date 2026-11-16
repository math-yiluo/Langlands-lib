# The analytic continuation and functional equation for `EqualData`

Module `Langlands.Global.RankinSelberg.EqualAnalyticMain`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

**`EqualData.main`**: for `D : EqualData F r` (`n = r + 1`) there are `σ₀`, `I` and `Ĩ` with:

1. for `Re s > σ₀`, the majorant integrals of `K_s = P |det|^s Θ(Φ, ·)` and of
   `K̃_s = Pd |det|^s Θ(Φ̂, ·)` over `GL_n(F) \ GL_n(𝔸)` are finite, and `I(s) = ∫ K_s`,
   `Ĩ(s) = ∫ K̃_s`;
2. `I` has at most simple poles in `equalPoleSet F n χ`, and `Ĩ` in `equalPoleSet F n χ⁻¹`;
3. `I` is bounded in vertical strips away from `equalPoleSet F n χ`;
4. `I(s) = Ĩ(1 - s)` for all `s`.

## Construction

By `ideleChar_dichotomy`:

- **If `χ = |·|^w`**, with `C = C_w` (`residueConstant`):
  `I(s) = A(s) + Ã(1-s) + Φ̂(0) C/(n(s-1) + w) - Φ(0) C/(n s + w)` and
  `Ĩ(s) = Ã(s) + A(1-s) - Φ(0) C/(n(1-s) + w) + Φ̂(0) C/(-n s + w)`.
  For `Re s > σ₀(w)` (`σ₀`, `conditions`), `integral_kernel_eq` and `integral_dual_kernel_eq`
  hold, and the residual integrals are evaluated by `residueLt_eq_of_char` and
  `residueGe_eq_of_char`. The poles `-w/n`, `1 - w/n` of `I` and `w/n`, `1 + w/n` of `Ĩ` lie in
  `equalPoleSet F n χ` and `equalPoleSet F n χ⁻¹`. The latter holds because
  `χ⁻¹ = |·|^(-w)` (`ideleChar_inv_eq`). `hasAtMostSimplePolesIn_two` and
  `boundedInVerticalStripsAwayFrom_two` apply with the entire parts `A(s) + Ã(1-s)` and
  `Ã(s) + A(1-s)` (`differentiable_G`, `differentiable_Gd`, `bounded_G`).
- **Otherwise** the residual integrals vanish (`residueLt_eq_zero`, `residueGe_eq_zero`).
  Then `I(s) = A(s) + Ã(1-s)` and `Ĩ(s) = Ã(s) + A(1-s)` are entire.

In both cases `Ĩ(1 - s) = I(s)` is an algebraic identity of the formulas.

## Provenance

The structure, an entire part plus simple fractions at `-w/n` and `1 - w/n`, is that of
Cogdell 2004, §2.3, printed pp.209–211 (the term `o(s)` and Theorem 2.2). The proof is
internal.
