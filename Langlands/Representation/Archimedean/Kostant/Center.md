# Central elements of `U(∏ᵢ 𝔤𝔩_{n i})` with prescribed symbols

`GLProd K n = ∀ i, Matrix (Fin (n i)) (Fin (n i)) K` carries the commutator bracket. Its basis
`glBasis` consists of the matrix units `unit i p q = Pi.single i (Matrix.single p q 1)`, and
`gen i p q` is the image of `unit i p q` in `U`.

* `lie_unit`: `⁅x, E_rq⁆ = ∑_a x_{ar} E_aq - ∑_b x_{qb} E_rb` in block `i`.
* `pw i k p q` is the `(p, q)` entry of the `k`-th power of the matrix `genMat i` of generators.
  It satisfies Gelfand's rule `[x, E^k] = [xᵀ, E^k]`, with `xᵀ` acting through scalars
  (`adMat_pow`). Hence `gel i k = tr(E^k)` is central (`gel_mem_center`).
* `symbol_gel`: the symbol of `gel i k` is `tr(Xᵢ^k)`, the trace of the `k`-th power of the
  generic block.
* `zk i k` is defined by `Z_0 = 1` and `Z_k = -(1/k) ∑_{j<k} Z_j C_{i,k-j}`. It is central and
  lies in `U_k`. By `newton_identity`, its symbol is the coefficient of `t^{n i - k}` in the
  characteristic polynomial of the generic block (`symbol_zk`).
