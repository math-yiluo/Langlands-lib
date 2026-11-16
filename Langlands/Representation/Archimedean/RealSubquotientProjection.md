# The principal-series projection of `U(𝔤) ⊗ ℂ^d`

Module: `Langlands.Representation.Archimedean.RealSubquotientProjection` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is a helper module for the proof of `RealPrincipalSeriesSubquotientStatement`; see
`RealPrincipalSeriesSubquotientProof.md` for the overall argument. Throughout, `τ` is a matrix
representation of `O(n)` on `ℂ^d`, and `D` satisfies `IsTypeDerivative τ D`. Most results also
assume `τ` is continuous. `UU n` is the enveloping algebra `U(𝔤)` of `𝔤 = LL n = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`.

This module replaces the Harish-Chandra projection `p : U(𝔤) → U(𝔞) ⊗ U(𝔨)` of Wallach, *Real
Reductive Groups I*, 3.5.6–3.5.8, which rests on Poincaré–Birkhoff–Witt independence. Instead,
polynomial representatives are built by induction on word length and made unique by separating
them with principal series (`Represents.unique`).

## Symbols and the Iwasawa splitting of `𝔤`

- `realSymbol n`: symbol data for `U(ℂ ⊗ 𝔤𝔩_n(ℝ))`, transported from the Library's
  `Kostant.glSymbol` along `toGL`. `realSymbol_ξ_tmul` computes the symbol of a generator
  `z ⊗ X` as `∑_{p,q} z X_{pq} X_{pq}` (coordinate variables).
- `diagRes n` restricts a polynomial on `𝔤𝔩_n(ℂ)` to the diagonal matrices. `diagLin x` is the
  diagonal restriction of the symbol of `x`, so `eval a (diagLin (z ⊗ X)) = z ∑ⱼ aⱼ Xⱼⱼ`
  (`eval_diagLin_tmul`). This is the character `ℓ_a` of the upper triangular Borel subalgebra.
- `upL n`, `skL n`: the complex-linear extensions of `RealJacquetFrobenius.upperPart` and
  `skewPart`, with `upL n x + skL n x = x`. `Dc D` is the complex-linear extension of `D`.
- `eval_one_upL`: on `PS a e`, `(R(upL x) G)(1) = ℓ_a(x) G(1)`. This follows from
  `rightDerivative_upper_apply_one`.
- `apply_skL_intertwiner`: `π(skL x)(T v) = T(Dc D (skL x) v)` for a `K`-intertwiner `T`.

## Polynomial representatives

- `psAct a e : UU n →ₐ[ℂ] End(PS a e)` is the enveloping action of the Library's
  `realStandardLie`.
- `lam a e T u v := (psAct a e u (T v))(1)`.
- `lam_ι_mul`: write `x = upL x + skL x`. Then
  `λ_T(x u, v) = ℓ_a(x) λ_T(u, v) + λ_T(skL x · u - u · skL x, v) + λ_T(u, Dc D (skL x) v)`.
- `Represents τ u v q`: `q ∈ ℂ[a₁..aₙ]^d` represents `(u, v)` when `λ_T(u, v) = (T(q(a)))(1)`
  for all `a`, `e` and all `T ∈ gkIntertwiners (realStandardRep n (psList a e)) d τ`.
- `exists_represents`: every `u` in the span of words of length `≤ m` has, for every `v`, a
  representative of total degree `≤ m`. Its degree-`m` part is `diagRes(σ_m(u)) · v`, where
  `σ_m` is the symbol. The proof is by induction on `m` using `lam_ι_mul`; the commutator term
  stays in filtration degree `m`.
- `Represents.unique` (needs continuous `τ`): two representatives agree. Their difference
  `r(a)` satisfies `φ(r(a)) = 0` for every sign functional `φ` of every sign vector `e`
  (`exists_frobenius_intertwiner`), so `r(a) = 0` for all `a` (`eq_zero_of_signFunctional`).
  Then `r = 0` by `MvPolynomial.funext`.
- `Q τ u v`: the representative (chosen; zero if none exists). Lemmas: `Q_represents`, `Q_eq`,
  additivity and homogeneity in `u` and in `v` (`Q_add`, `Q_smul`, `Q_add_right`,
  `Q_smul_right`, `Q_sum_right`). `Q_degree`: on `U_m` (`degreeFiltration`), `Q` has degree
  `≤ m` with top part `diagRes(σ_m(u)) · v`. `Q_mul_skew`: `Q(u · (1 ⊗ Y), v) = Q(u, D(Y) v)`
  for antisymmetric `Y`.

## Matrices over `U(𝔤)` acting on intertwiners

- `act P b T` (for an algebra map `P : UU n →ₐ End M`): the linear map with
  `(b · T)(eᵢ) = ∑ⱼ P(bᵢⱼ) T(eⱼ)`. Lemmas: `act_apply`, `act_single`, `act_ext`,
  `act_mul` (`(b b') · T = b · (b' · T)`), `act_scalar` (scalar matrices act through the
  transpose), `comp_act`.
- `InB τ b`: `b` is `K`-invariant, `τ(k)ᵀ b = Ad(k)(b) τ(k)ᵀ` for all `k ∈ O(n)`. These are
  Wallach's `(U(𝔤) ⊗ End(V_γ))^K`, written as matrices.
- `act_mem`: if `ρ(k) P(u) = P(Ad(k) u) ρ(k)`, then `K`-invariant matrices map `K`-intertwiners
  to `K`-intertwiners.
- `chat τ b` (`ĉ(b)`): the `d × d` polynomial matrix with columns `∑ⱼ Q(bᵢⱼ, eⱼ)`.
  `eval_one_act_psAct`: `((b · T) x)(1) = (T(ĉ(b)(a) x))(1)` on `PS a e`. `chat_mul`:
  `ĉ(b b') = ĉ(b') ĉ(b)` when `b'` is `K`-invariant, the analogue of Wallach 3.5.6 (2).

## Central elements

- `Jideal a`: the span of the `ι(c ⊗ X) u - ℓ_a(c ⊗ X) u` for upper triangular `X`.
- `exists_sub_mem_Jideal`: every central `z` is congruent to a scalar modulo `Jideal a`. The
  proof applies the Library's `JacquetCenter.exists_comp_envelopingAction_eq_smul` to the
  left-multiplication action `lmulRep n` of `𝔤` on `U(𝔤)`, for every linear functional vanishing
  on `Jideal a`.
- `eval_one_psAct_Jideal`: `Jideal a` acts by zero after evaluation at `1` on `PS a e`.
- `exists_eval_one_central`: a central `z` acts on evaluation at `1` of `PS a e` by one scalar,
  independent of `e`.
- `exists_Q_central`: for central `z` there is a polynomial `ξ` with `Q(z, v)ᵢ = ξ · vᵢ`. This
  replaces Wallach's computation 3.5.7 (1), which uses the Harish-Chandra homomorphism.
