# Valuations of the root datum of the diagonal torus of `GL_N`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.Valuation`, namespace
`Langlands.Geometry.Building.GeneralLinearParahoric`.

Let `F` be a nonarchimedean local field and `A : KPApartmentData (diagTorus F N)
(localFieldOrder F)` apartment data for the diagonal torus of `GL_N`, normalized by
`ω = localFieldOrder F` (the order `ord`, with `ord ϖ = 1`). A point `x` of the apartment is a
valuation `φ = x.val` of the root datum (Kaletha–Prasad, Definition 6.1.2). The module computes
`φ` explicitly.

## Matrices and torus points (any field)

- `instMonoDiagTorus`: the diagonal torus is a monomorphism (it is a maximal split torus,
  `GeneralLinear.isMaximalSplitTorus_diagonalTorus`).
- `transvectionPoint hkl t`: the rational point of `GL_N` with matrix `1 + t E_{kl}`, `k ≠ l`;
  `transvectionPoint_zero`, `transvectionPoint_ne_one` (for `t ≠ 0`), `transvectionPoint_mul`
  (`(1 + s E_{kl})(1 + t E_{kl}) = 1 + (s + t) E_{kl}`), `transvectionPoint_inv`.
- `torusPoint d`: the rational point of the diagonal split torus with coordinates
  `d : Fin N → Fˣ`; `toMatrixGL_map_torusPoint`: its image in `GL_N` is `diag(d)`.
- `torusPoint_inv_conj_transvectionPoint`: `d⁻¹ (1 + t E_{kl}) d = 1 + d_k⁻¹ t d_l E_{kl}`.
- `prod_zpow_single_sub`, `rationalCharacterEval_rootCharacter_torusPoint`: the character
  `e_k − e_l` takes the value `d_k d_l⁻¹` on `torusPoint d`.
- `localFieldOrder_inv`, `localFieldOrder_mul`, `localFieldOrder_neg_one`: `ord` is a
  homomorphism and `ord(−1) = 0`.

## The valuation on root groups

- `transvectionPoint_mem_rootGroupPoints`: every transvection `1 + t E_{kl}` lies in the root
  group of `e_k − e_l`. Some point `u = 1 + t₀ E_{kl}` of the root group has a finite value
  (`IsRootDatumValuation.exists_ne_top`; root group points are transvections by
  `exists_eq_transvectionGL_of_mem_rootGroupPoints`), and conjugating it by a diagonal torus
  point gives `1 + t E_{kl}`; the split-torus compatibility of `φ`
  (`isSplitTorusCompatible`, part of axiom V 6) shows that the conjugate also has a finite value,
  so it lies in the root group.
- `rootValue A x k l`: the real number `c_{kl}(x) = φ_{e_k − e_l}(1 + E_{kl})` (and `0` for
  `k = l`); `val_transvectionPoint_one` records that this value is finite.
- `val_transvectionPoint`: **`φ_{e_k − e_l}(1 + t E_{kl}) = ord(t) + c_{kl}(x)` for `t ≠ 0`**,
  from split-torus compatibility applied to the torus point `diag(1, …, t, …, 1)` (entry `t` at
  `l`).

## Antisymmetry and additivity

- `map_torusPoint_mem_centralizerPoints`, `toMatrixGL_permPoint`,
  `transvectionPoint_rotation_eq`, `transvectionPoint_rotation_mem_normalizerPoints`: the
  product `(1 − E_{lk})(1 + E_{kl})(1 − E_{lk})` is a permutation matrix times a diagonal
  matrix, hence normalizes the diagonal torus.
- `neg_rootCharacter`, `rootCharacter_add`: `−(e_k − e_l) = e_l − e_k` and
  `(e_i − e_j) + (e_j − e_k) = e_i − e_k`.
- `rootValue_swap`: **`c_{lk}(x) = −c_{kl}(x)`**, from axiom V 5 (`IsRootDatumValuation.opposite`)
  applied to `u = 1 + E_{kl}` and `u′ = u″ = 1 − E_{lk}`.
- `commutatorElement_transvectionPoint`: the commutator of `1 + E_{ij}` and `1 + E_{jk}` is
  `1 + E_{ik}` for distinct `i, j, k`.
- `eq_one_of_nsmul_add_nsmul_mem`: the only positive combination `p (e_i − e_j) + q (e_j − e_k)`
  that is a root has `p = q = 1`.
- `rootValue_add_le`: `c_{ij}(x) + c_{jk}(x) ≤ c_{ik}(x)` for distinct `i, j, k`, from axiom V 3
  (`IsRootDatumValuation.commutator`).
- `rootValue_add`: **`c_{ik}(x) = c_{ij}(x) + c_{jk}(x)` for all `i, j, k`**, combining
  `rootValue_add_le` with its reverse obtained through `rootValue_swap`.
- `exists_rootValue_eq_sub`: there are real numbers `y_k` with `c_{kl}(x) = y_k − y_l`
  (`y_m = c_{m0}(x)`).

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge University
Press, 2023: Definition 6.1.2 (the axioms V 0–V 6 of a valuation of the root datum) and §15.1
(for `GL_N` the valuations are `φ_{kl}(1 + t E_{kl}) = ord t + y_k − y_l`). Literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`. The computation here is derived directly from
the axioms as they are stated in `IsRootDatumValuation` and `IsSplitTorusCompatible`.
