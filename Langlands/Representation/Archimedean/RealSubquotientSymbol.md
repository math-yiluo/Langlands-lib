# Symbols and the injectivity of the principal-series projection

Module: `Langlands.Representation.Archimedean.RealSubquotientSymbol` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is a helper module for the proof of `RealPrincipalSeriesSubquotientStatement`; the overall
argument is in `RealPrincipalSeriesSubquotientProof.md`. Its main result is the injectivity
statement `act_eq_zero_of_chat_eq_zero`. If a `K`-invariant matrix `b` over `U(𝔤)` has
`ĉ(b) = 0`, then `b` acts by zero on every `K`-intertwiner from `τ` into every
`(𝔤𝔩_n(ℝ), O(n))`-module. It corresponds to Wallach, *Real Reductive Groups I*, Lemma 3.5.9
(if `u ∈ U(𝔤)^K` and `p_γ(u) = 0` then `u ∈ U(𝔤) I_γ`). Wallach proves it with the
symmetrization `S(𝔭) ⊗ U(𝔨) → U(𝔤)` and the restriction result 2.1.9. Here it is proved with the
Library's symbol calculus (`Kostant`), ordered spanning, and the spectral theorem, which plays the
role of 2.1.9.

## An adapted basis and ordered PBW spanning (Claim B)

- `theta n` is the real-linear automorphism `X ↦ X - Lᵀ` of `𝔤𝔩_n(ℝ)`, where `L` is the strictly
  lower part of `X`. `basisR n` and `bB n` are the bases it gives of `𝔤𝔩_n(ℝ)` and of
  `ℂ ⊗ 𝔤𝔩_n(ℝ)`. They consist of the `1 ⊗ E_pq` for `p ≤ q` and the `1 ⊗ (E_pq - E_qp)` for
  `p > q` (`bB_apply`).
- `psiB n` and `symB n`: symbols written in the coordinates of `bB`
  (`symB_symbol`, `symB_ξ_basis`).
- `bsList n` lists the basis indices with the upper-triangular ones first and the antisymmetric
  ones last. `orderedMonomial_eq_mul` shows that an ordered monomial containing an antisymmetric
  letter is a word times that letter on the right.
- `yfun y` is a real point whose antisymmetric coordinates are `0`.
- `mem_of_symbol_vanish`: let `u ∈ U_{D+1}`, and suppose its degree-`(D+1)` symbol vanishes at
  every `yfun y`. Then `u ∈ U_D + span{v · (1 ⊗ (E_pq - E_qp)) : v ∈ U_D, p > q}`. The proof
  uses the Library's ordered spanning `Kostant.degreeFiltration_le_orderedSpan` (no PBW
  independence is needed) together with `MvPolynomial.funext` at real points.

## Equivariance and the spectral theorem

- `evMat S` evaluates a polynomial on `𝔤𝔩_n(ℂ)` through the pairing `X ↦ tr(X S)`
  (`evMat_ξ_tmul`).
- `evMat_symbol_conj`: `evMat S (σ_N(Ad(k) u)) = evMat (kᵀ S k) (σ_N(u))`.
- `eval_diagRes`: evaluating a diagonal restriction at real `t` is `evMat (diag t)`.
- `symMat y` is a real symmetric matrix, and `eval_yfun_symB` gives
  `eval (yfun y) (symB-symbol) = evMat (symMat y) (realSymbol-symbol)`.
- `exists_orth_diag` (**spectral theorem**): a real symmetric `S` is `kᵀ diag(t) k` for some
  `k ∈ O(n)`. It uses `Matrix.IsHermitian.spectral_theorem`.
- `typeDerivative_conj`: `τ(k) D(Y) = D(k Y kᵀ) τ(k)` for antisymmetric `Y`.

## The relations and the descent

- `Kspan D ⊆ U(𝔤)^d` is the span of `x ⊗ (u·(1 ⊗ Y)) - (D(Y) x) ⊗ u` for antisymmetric `Y`,
  written as `d`-tuples.
- `PhiT P T w = ∑ⱼ P(wⱼ) T(eⱼ)`. `PhiT_Kspan`: `Φ_T` kills `Kspan D` for every `K`-intertwiner
  `T` into a `(𝔤𝔩_n(ℝ), O(n))`-module (by `apply_skew_intertwiner`).
- `QQ τ w = ∑ⱼ Q(wⱼ, eⱼ)`. It is linear (`QQ_add`, `QQ_sub`, `QQ_smul`, `QQ_zero`), it vanishes
  on `Kspan D` (`QQ_Kspan`, by `Q_mul_skew`), it is the identity on constants (`QQ_const`), and
  its top part is the diagonal restriction of the symbol (`QQ_degree`).
- `psiVec b x = (∑ᵢ xᵢ bᵢⱼ)ⱼ`, with `QQ(psiVec b x) = ĉ(b) x` (`QQ_psiVec`).
- `gAct τ k w = (∑ₗ τ(k)ⱼₗ Ad(k)(wₗ))ⱼ` is the diagonal `O(n)`-action on `d`-tuples.
  `psiVec_conj`: `psiVec b (τ(k) x) = gAct k (psiVec b x)` for `K`-invariant `b`.
  `gAct_Kspan` (via `typeDerivative_conj`): `gAct` preserves `Kspan D`.
- `WN D N = Kspan D ⊔ (U_N)^d`. `single_mem_WN` transfers Claim B to tuples: the extra terms
  `v·(1 ⊗ Y)` placed in coordinate `l` are `Kspan` relations plus elements of `U_N`.
- `psiVec_mem_Kspan` (**descent**): let `b` be `K`-invariant with `ĉ(b) = 0`. Then
  `psiVec b x ∈ Kspan D` for every `x`. Suppose all `psiVec b y` lie in `WN D (N+1)`. Write
  `psiVec b y = κ + w(y)` with `κ ∈ Kspan D` and `w(y) ∈ (U_{N+1})^d`, linear in `y`. For a
  real symmetric `S = kᵀ diag(t) k`, the vector `v_l = evMat S (σ_{N+1}(w(y)_l))` satisfies
  `τ(k) v = 0`. This follows from `QQ(gAct k (w y)) = 0`, `QQ_degree` and `evMat_symbol_conj`.
  So `v = 0`, and Claim B puts `w(y)` in `WN D N`. Descending from a level containing all
  entries of `b` reaches `WN D 0`. There the `U_0`-part is a constant vector killed by `QQ`,
  hence zero.
- `act_eq_zero_of_chat_eq_zero` (**injectivity**): for continuous `τ` with derivative `D`,
  `K`-invariant `b` and `ĉ(b) = 0`, `act (envelopingAction π) b T = 0` for every
  `K`-intertwiner `T` from `τ` into every `(𝔤𝔩_n(ℝ), O(n))`-module. Each row of `b` is in
  `Kspan D`, which `Φ_T` kills.
