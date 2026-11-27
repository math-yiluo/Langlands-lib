# A generator of a cyclic algebra is an isometry of the local norm

Module `Langlands.BaseChange.TwistedLocalDescent.SigmaIsometry`. Let `E` be a nonarchimedean local
field which is an algebra over a topological field `F`, with the `F`-module topology, normed by
`LocalGalois.localNormedField`.

- `continuous_algEquiv`: every `F`-algebra automorphism of `E` is continuous (it is `F`-linear and
  `E` has the module topology).
- `norm_lt_one_of_algEquiv`, `norm_lt_one_iff_algEquiv`: `‖σ x‖ < 1 ↔ ‖x‖ < 1`, since
  `‖x‖ < 1` iff `x^k → 0` and `σ` is continuous.
- `norm_lt_norm_iff_algEquiv`: `σ` preserves the strict order of norms (apply the previous item
  to `x / y`).
- `norm_algEquiv_eq`: if `σ^l = 1` with `l > 0`, then `‖σ x‖ = ‖x‖`. If `‖σ x‖ < ‖x‖`, the norms
  `‖σ^k x‖` would decrease strictly in `k`, contradicting `σ^l x = x`; similarly for `>`.
