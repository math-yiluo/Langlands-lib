# Inputs for the Eichler decomposition in Witt index one

Module `Langlands.GroupScheme.Quaternionic.WittIndexOneInputs`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.Eichler`.

This module supplies the hypotheses used by `HyperbolicLevi` and `EichlerReducedNorm`, in the
setting of the quaternionic Kneser–Tits statement. Throughout, `q` is a Tits `σ`-quadratic
form on row vectors `D^n`, `h` is its polar form, and `(e, f)` is a hyperbolic pair
(`IsHyperbolic`: `q(e) = q(f) = 0` and `h(e, f) = 1`).

## Results

* `eq_zero_of_ortho_of_quadraticWittIndex_le_one`: if `quadraticWittIndex q ≤ 1`, then every
  `y` with `h(y, e) = h(y, f) = 0` and `q(y) = 0` is zero. In other words, `{e, f}^⊥` is
  anisotropic.
  *Proof.* Otherwise `span_D {e, y}` is totally singular, because
  `q(a e + b y) = [a h(e, y) σ(b)] = 0`. It has dimension `2`: `e` and `y` are linearly
  independent, as pairing with `f` shows. This contradicts
  `IsTotallySingular.finrank_le_quadraticWittIndex`.
* `pairFunctional σ q e f`: the `D`-linear map `v ↦ (h(v, e), h(v, f))` from `D^n` to `D × D`.
* `exists_ne_zero_ortho`: if `card n ≥ 3`, some nonzero `x` satisfies `h(x, e) = h(x, f) = 0`.
  *Proof.* Rank–nullity for `pairFunctional`, whose range has dimension at most `2`.
* `exists_ne_zero_mem_alternatingSubspace`: if `dim_K D = 4` and `dim_K D^σ = 3`, then the
  alternating subspace `{a - σ(a)}` contains a nonzero element.
  *Proof.* It is the range of `id - σ`, whose kernel is `D^σ`; rank–nullity gives dimension
  `1`.
* `reducedDegree_eq_two`: if `dim_K D = 4`, then `reducedDegree K D = Nat.sqrt 4 = 2`.

## Provenance

Internal; elementary linear algebra, used for Task 5398. Together with `HyperbolicLevi` and
`EichlerReducedNorm`, these results apply to the forms of the target statement. Those forms
are on `D^4` or `D^5`, have Witt index `1`, and are defined over a quaternion division algebra
with `dim_K D^σ = 3`.
