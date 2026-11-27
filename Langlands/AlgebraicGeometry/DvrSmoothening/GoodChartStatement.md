# Closures of points of ramification index one have good charts

The module `Langlands.AlgebraicGeometry.DvrSmoothening.GoodChartStatement` contains one
proposition, `GoodChartStatement`, and proves nothing.

## The proposition

`GoodChartStatement` quantifies over a universe `u`, a discrete valuation ring `R`, an
`R`-algebra `A` of finite type, an ideal `J` of `A` and a set `S` of ideals of `A`. Its
hypotheses are

1. `J = sInf S` and `S` is non-empty;
2. every `p ∈ S` is `ψ⁻¹(𝔪_{R''})` for some discrete valuation ring `R''` in universe `u` with
   a local homomorphism `R → R''` satisfying `IsRamificationIndexOne R R''` and some
   `ψ : A →ₐ[R] R''`.

So `V(J)` is the closure, with its reduced structure, of the closed points of points of
ramification index one, and lies in the special fibre. The conclusion is an element `s ∉ J`
such that for every localization `A'` of `A` away from `s` (an `R`-algebra compatibly with
`A`):

- `k ⊗_R (A' ⧸ J A')` is smooth over the residue field `k` of `R` (it is `A' ⧸ J A'` itself,
  since `J` contains the maximal ideal of `R`);
- `(A' ⧸ J A') ⊗_{A'} Ω_{A'/R}` is a free `A' ⧸ J A'`-module.

Since `s ∉ J` and `J` is radical, the open `D(s)` meets `V(J)`: on the non-empty open
`V(J) ∩ D(s)` the reduced closed subscheme `V(J)` is smooth over `k` and the restriction of
`Ω_{Spec A/R}` to it is free.

## Source

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models` (SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is PDF
page `p + 7`):

- §3.3, property (N) and Lemma 4, printed p. 67: if the `k_s`-valued points of `Y_k` lifting to
  `R^{sh}`-valued points of `X` are schematically dense in `Y_k`, then `Y_k` is geometrically
  reduced and its smooth locus is open and dense.
- §3.4, printed p. 71: for an `E`-permissible `Y_k`, "the largest open subscheme `U_k` of `Y_k`
  which is smooth over `k` and where `Ω¹_{X/R}|_{Y_k}` is locally free … is always Zariski-dense
  in `Y_k` due to Lemma 3.3/4".

Here the role of the `k_s`-points lifting to `R^{sh}`-points is played by the closed points of
points with values in discrete valuation rings of ramification index one (BLR 3.6, Definition 1,
printed p. 78); their residue fields are separable over `k`, which is what Lemma 3.3/4 uses.
The proposition asserts non-emptiness of `U_k` in the affine case, in the form of a basic open
on which both conditions hold.
