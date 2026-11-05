# Recovering the coefficients of an ordered product

Author: Worker 1398.

Over any commutative algebra `R` over a field `F`, matrices `xm j s = divExp (e j) s` and
ordered products `opm l c`. `IsSUnip S M` (diagonal `1`, off-diagonal weight differences in
`S`) is preserved by products when `S` is additively closed with positive `ℓ`; ordered products
over a list `l` have this property for `sSet l`, the positive combinations of roots of `l`
(`isSUnip_opm`). If the roots of `l` have levels at least that of `γ` and `γ ∉ l`, then `root γ`
is not in `sSet l` (`root_not_mem_sSet`), so the entry of `x_γ(s) ∏_l x(c)` at a position of
weight difference `root γ` is `s · (e γ 1)` (`xm_mul_opm_apply`).

`posEntry F γ` is a position where `e γ 1` is nonzero in `F`, `κ γ` the inverse of that entry.
`retrAux` reads the coefficients along a list, removing each factor after reading it; `retr`
does this along `posList`. `retr_opm`: `retr (opm posList c) = c` on positive roots (and `0`
elsewhere); `retr_map`: `retr` commutes with `F`-algebra homomorphisms. These make the
coefficients polynomial functions of the entries.

Over the dual numbers (`GeneralLinear.DualNumber.epsilonMatrix X = X.map inr`):
`opm l (inr ∘ c) = 1 + ε (Σ c j • e j 1)` (`opm_inr`). `mem_span_of_opm_retr`: if
`1 + εX = opm posList (retr (1 + εX))` then `X` lies in the `F`-span of the `e γ 1`, `γ`
positive; the recovered coefficients have zero constant part because `retr` commutes with
reduction and `retr 1 = 0`. This is the first-order part of the big-cell coordinates (Steinberg,
*Lectures*, §5); the argument here is internal.
