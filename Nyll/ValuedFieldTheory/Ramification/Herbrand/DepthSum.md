# The Herbrand function as a sum of truncated depths

Module `Nyll.ValuedFieldTheory.Ramification.Herbrand.DepthSum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G` with a decreasing filtration `(G_n)` by normal subgroups and a depth function `i : G → ℕ∞` that cuts out the filtration, the file proves the classical formula `φ(s) = (1/|G_0|) Σ_(σ∈G) min(i(σ), s + 1) − 1` for every real `s ≥ −1`, where `φ` is the normalized Herbrand function of the filtration.

## Main declarations

- `truncateENatAtDVF i r`: `min(i, r)` as a real number, with `i = ∞` sent to `r`.
- `herbrandFunction_eq_depth_sum_of_mem`: the formula above. The hypothesis `hmem` says that `σ ∈ G_n` exactly when `n + 1 ≤ i(σ)`, for all `n` and `σ`.
- Helper lemmas under the same hypothesis: elements outside `G_0` contribute 0 when `s ≥ −1` (`truncate_depth_eq_zero_of_not_mem_lower_zero`), so the sum may be taken over `G_0` (`sum_truncate_depth_eq_sum_lower_zero_of_mem`). For `s ∈ [m, m+1]`, each term over `G_0` is `1 + truncatedLowerDepth m σ + (s − m)·[σ ∈ G_(m+1)]`, and the sum over `G_0` is `|G_0| + Σ truncatedLowerDepth m σ + (s − m)·|G_(m+1)|`.

## Proofs

For `s ≥ 0` the result follows from the depth-sum form of `φ` on `[m, m+1]` proved in `Herbrand.Function`. For `−1 ≤ s < 0`, every element of `G_0` has depth at least 1, so each term equals `s + 1`.

## Watch for

- The link between the filtration and the depth is the hypothesis `hmem`; here it does not come from a valuation. With this convention, `G_n` is the set of elements of depth at least `n + 1`.
- The formula is proved only for `s ≥ −1`, although `φ` is defined on all of `ℝ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Herbrand/DepthSum.lean`: the Lean file is the source byte for byte (SHA-256 `1e2811ea2dad729dc6593a982572405bf77a9fd8136c24283259c50222b45ed5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
