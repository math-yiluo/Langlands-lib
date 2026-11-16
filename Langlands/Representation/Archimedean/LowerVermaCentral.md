# Central characters of lower Verma modules of `𝔤𝔩_n(ℂ)`

Module `Langlands.Representation.Archimedean.LowerVermaCentral`, namespace
`Langlands.Archimedean.VermaCentral`. It imports `LowerVermaPBW` (Poincaré–Birkhoff–Witt basis
`basisU`, functionals `Ψ_v`, `gen_ne_zero`, `lowerVermaWeight`) and the Library modules
`ComplexJacquetFinite` (Gelfand's recursion `gelPoly`, `comm_pow`, `diag_pow`, `boxSet`),
`Kostant.OrbitVanishing` (coadjoint derivations and `conj_mem_zeroSet`) and
`Automorphic.AssociatedGammaTriangular` (`exists_triangularizing_cyclic`).

The main result is `lowerVermaCentral : VermaGL.CentralCharacterStatement`. The statement is in
the Library module `LowerVerma`. For every `n` and every algebra map `χ : Z → ℂ` from the center
`Z` of `U = U(𝔤𝔩_n(ℂ))` there is a weight `λ : Fin n → ℂ` such that

* every `z ∈ Z` acts on the generator of `M⁻(λ)` by `χ(z)`: `z • gen λ = χ(z) • gen λ`;
* `λ` is `Z`-extremal (`VermaGL.IsZExtremal`): for every `μ ≠ λ` with `λ - μ ∈ Q₊` some central
  `z` and scalar `c` satisfy `z • gen λ = c • gen λ` and `z • gen μ ≠ c • gen μ`.

This is Harish-Chandra's theorem in the form used by Bernstein–Gelfand 1980, 1.6, together with
the finiteness of linkage classes (see the paired Markdown of `LowerVerma`). The Lean proof does
not identify the image of the Harish-Chandra map with the Weyl group invariants. It only uses:
the map is an injective algebra map into `ℂ[λ] = MvPolynomial (Fin n) ℂ`, and `ℂ[λ]` is a
finite module over its image. These two facts give lying over (every `χ` is attained) and
finite fibres; a weight of minimal height in the fibre is then `Z`-extremal. Everything is
proved, with no new axioms.

## 1. The Harish-Chandra map (section `HC`)

* `Xd n c` is `X_p` on a diagonal index `c = (p, p)` and `0` otherwise.
  `gam n : U →ₗ ℂ[λ]` is the linear map with `γ(E^α) = ∏ Xd(c)` over the letters `c` of the
  PBW monomial `E^α` (`Basis.constr`; `gam_basisU`). So `γ(E^α)` is the monomial of the diagonal
  letters if `E^α` has only diagonal letters, and `0` otherwise.
* `eval_Xd`, `eval_gam`: `γ(u)(λ) = Ψ_{vVal λ 0}(u)` for every `u ∈ U` and every `λ`. Here
  `vVal λ 0` is `λ_p` on `(p, p)` and `0` on all other indices.
* `center_smul_gen`: a central `z` acts on `gen λ` by `γ(z)(λ)`. By `lowerVermaWeight`,
  `z • gen λ = c • gen λ` for some `c`, because `z • gen λ` has weight `λ`. Then
  `z - c ∈ lowerVermaIdeal λ`, and `Ψ_{vVal λ 0}` kills that ideal
  (`Psi_mul_mem_lowerVermaIdeal`), so `c = Ψ(z) = γ(z)(λ)`.
* `gam_one`; `gamC n : Z →ₐ ℂ[λ]` is `γ` restricted to the center. It is multiplicative because
  both `γ(zw)(λ)` and `γ(z)(λ) γ(w)(λ)` are the scalar by which `zw` acts on `gen λ ≠ 0`, for
  every `λ` (`MvPolynomial.funext`). `eval_gamC_smul_gen` restates `center_smul_gen`.

## 2. Gelfand's central elements (section `Gelfand`)

* `Gm n` is the matrix `(E_pq)` with entries in `U`, and `gel n k = Σ_p (Gm^k)_pp`.
* `unitU_comm`: `[E_ab, E_cd] = δ_bc E_ad - δ_da E_cb` in `U`.
* `eL a b` is left multiplication by `E_ab`, and `isGlFamily_eL` says it satisfies these
  relations (Library `ComplexJacquetFinite.IsGlFamily`). `eL_pow_apply` identifies the powers
  of the matrix `(eL a b)` with left multiplication by `(Gm^k)_xy`. The Library's `comm_pow`
  then gives `[E_ac, (Gm^k)_xy] = δ_xc (Gm^k)_ay - δ_ay (Gm^k)_xc`. Summing over `x = y`
  gives `unitU_mul_gel`: every `E_ac` commutes with `gel k`, and `gel_mem_center` follows
  (Library `Kostant.mem_center_of_commute`).
* `eR a b` is right multiplication by `E_ba`. It is again a `𝔤𝔩_n` family (`isGlFamily_eR`), and
  `eR_pow_apply` identifies the powers of `(eR a b)` with `v ↦ v (Gm^k)_yx`. The diagonal
  operators `dR a = eR a a` commute (`dR_commute`). `dAlg` is the commutative subalgebra they
  generate, and `psiR : ℂ[λ] →ₐ End U` sends `X_a` to `v ↦ v E_aa` (`psiR_X`).
* `Psi_psiR`: `Ψ_{vVal λ 0}(ψ_R(f) v) = f(λ) Ψ_{vVal λ 0}(v)`, by induction on `f`, using right
  `𝔟⁻`-equivariance of `Ψ` (`Psi_mul_unitE_lo`).
* `Psi_gel`: `Ψ_{vVal λ 0}(gel k) = Σ_a g_k(a)(λ)`, where `g_k(a)` are the polynomials
  `ComplexJacquetFinite.gelPoly n k a` with `g_0(a) = 1` and
  `g_{k+1}(a) = (X_a + a) g_k(a) - Σ_{c < a} g_k(c)`. Apply the Library's `diag_pow` to the
  family `eR`, with `N = ker Ψ` (which contains `v E_ba` for `a < b` and is stable under
  `v ↦ v E_aa`), at `v = 1`.
* `gam_gel`: `γ(gel k) = Σ_a g_k(a)`.

## 3. `ℂ[λ]` is finite over the image of `γ` (sections `Integral`, `Newton`, `Box`, `HCIntegral`)

For a subalgebra `A ⊆ ℂ[σ]`, `Tf A d` is the `A`-span of the polynomials of total degree `≤ d`.
`mem_Tf_of_le`, `Tf_mono`, `mem_Tf_of_mem` (`A ⊆ T_0`), `Tf_mul` (`T_d T_{d'} ⊆ T_{d+d'}`),
`C_mul_mem_Tf`, `neg_one_pow_mem_Tf` are the basic properties.

* `esymm_mem_Tf` (Newton's identities, `MvPolynomial.mul_esymm_eq_sum`): if every power sum
  `p_b` with `1 ≤ b ≤ n` lies in `T_{b-1}`, then every elementary symmetric polynomial `e_k` with
  `1 ≤ k ≤ n` lies in `T_{k-1}`. The proof is a strong induction on `k`.
* `xpow_mem_Tf`: under the same hypothesis `X_a^n ∈ T_{n-1}`. Evaluate
  `∏_b (X - X_b) = Σ_j (-1)^j e_j X^{n-j}` at `X = X_a`, where the product vanishes.
* `mem_span_box`: if `X_s^m ∈ T_{m-1}` for every `s`, then the monomials with all exponents
  `< m` (Library `boxSet`) span `ℂ[σ]` over `A`. The proof is a strong induction on total degree:
  a monomial with some exponent `≥ m` is `X^β · X_s^m`, and `X^β · T_{m-1}` consists of
  polynomials of smaller total degree.
* `imA n` is the range of `gamC n`. `gelSum_mem`: `Σ_a g_k(a) ∈ imA n`. `psum_mem_Tf`: the
  power sum `p_{k+1} = Σ_a X_a^{k+1}` lies in `T_k` over `imA n`, because
  `g_{k+1}(a) - X_a^{k+1}` has total degree `≤ k` (Library `totalDegree_gelPoly_sub`).
* `finite_imA`: `ℂ[λ]` is a finitely generated `imA n`-module (generated by the box monomials,
  `m = n`), hence `isIntegral_imA`: `ℂ[λ]` is integral over `imA n`.

## 4. `γ` is injective on the center (section `Injective`)

Let `z ∈ Z` with `γ(z) = 0`, and suppose `z ≠ 0`.

* Weight argument. `hD = ι(diag(dZero))` with `dZero = (0, -1, …, -(n-1))`. `hD_mul_W`,
  `hD_comm_basisU`: `[hD, E^α] = s(α) E^α`, where `sWt n α = s(α)` is the sum of
  `dZero_p - dZero_q` over the letters `(p, q)` of `E^α`. `repr_hD_comm`: the `α`-coordinate of
  `[hD, u]` is `s(α)` times that of `u`. `isDiag_of_sWt`: an exponent without strictly lower
  letters (`q < p`) and with `s(α) = 0` has only diagonal letters, since each upper letter
  contributes `q - p > 0`. (`prod_expand`, `sum_expand`, `not_mem_expand` rewrite list products
  over the letters of `E^α` as products over all indices.)
* `dgExp`, `gam_basisU_of_diag`, `gam_basisU_of_not_diag`, `coeff_gam`: for a diagonal exponent
  `α`, the coefficient of `X^{dgExp α}` in `γ(u)` is the `α`-coordinate of `u`.
* `exists_lower_letter`: since `z` is central, `[hD, z] = 0`, so every `α` in the support of `z`
  has `s(α) = 0`. If such an `α` had no strictly lower letter it would be diagonal, and its
  coordinate would be a coefficient of `γ(z) = 0`. So every PBW monomial in `z` has a strictly
  lower letter.
* Symbols. `sd n` is the Library symbol data `AssocSymbol.symbolData (stdB n)`.
  `symbol_basisU`: the degree-`N` symbol of `E^α` (`deg α ≤ N`) is `X^α` if `deg α = N` and `0`
  otherwise (Library `symbol_orderedMonomial`). `dx n x` is the derivation
  `X_c ↦ ξ⁅x, E_c⁆` of `ℂ[X_c : c ∈ Idx n]`. `dx_ξ`, `dx_isLeibniz` give the hypotheses of the
  Library's `symbol_commutator`, and `dx_symbol_center`: `dx x` kills the degree-`N` symbol of
  a central element of filtration degree `≤ N`.
* Transfer to the Library's coadjoint derivations. With a single block of size `n`
  (`nU n : Unit → ℕ`) and `eU n : Idx n → Coord (nU n)`, `dx_X`, `rename_dx_X` and `rename_dx`
  show that renaming variables along `eU` turns `dx(E_ab)` into
  `Kostant.coadDer (unit () a b)` (Library `coadDer_unit_X_same`).
* `exists_triangular`: every complex matrix `M` is conjugate to an upper triangular one. Choose
  `t` with `det(t - M) ≠ 0`, apply the Library's `exists_triangularizing_cyclic` to the cyclic
  group generated by the invertible matrix `t - M`, and recover `M = t - (t - M)`.
* `eq_zero_of_invariant`: a polynomial `σ` killed by all `dx(E_ab)` and vanishing on all upper
  triangular matrices vanishes at every matrix, hence is `0` (`MvPolynomial.funext`). The line
  `ℂ · rename(σ)` is stable under the coadjoint derivations, so its zero set is stable under
  conjugation (Library `Kostant.conj_mem_zeroSet`). Every matrix is conjugate to an upper
  triangular one, which lies in that zero set.
* `gamC_injective`: let `N` be the maximal degree of an exponent in the support of `z`, attained
  at `α₀`. The degree-`N` symbol `σ` of `z` is `Σ_{deg α = N} z_α X^α` (`symbol_basisU`), so its
  `X^{α₀}`-coefficient is `z_{α₀} ≠ 0`. Every monomial of `σ` contains a strictly lower variable
  (`exists_lower_letter`), so `σ` vanishes on upper triangular matrices. It is killed by the
  `dx(E_ab)` (`dx_symbol_center`). By `eq_zero_of_invariant`, `σ = 0`, a contradiction.

## 5. Central characters (section `Character` and the main theorem)

* `eqv n : Z ≃ₐ imA n` (`AlgEquiv.ofInjective`, `coe_eqv`). For a character `χ` of `Z`,
  `chiA n χ = χ ∘ eqv⁻¹` is the corresponding character of `imA n` (`chiA_eqv`).
* `fib n χ = {λ | ∀ z, γ(z)(λ) = χ(z)}`. `chiA_eval`: for `λ ∈ fib n χ`, `chiA χ` is evaluation
  at `λ` on `imA n`.
* `fib_nonempty` (lying over): `ker(chiA χ)` is a maximal ideal of `imA n`
  (`RingHom.ker_isMaximal_of_surjective`). Since `ℂ[λ]` is integral over `imA n`, some maximal
  ideal `Q` of `ℂ[λ]` lies over it (`Ideal.exists_ideal_over_maximal_of_isIntegral`). By the
  Nullstellensatz (`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`), `Q` is the ideal
  of a point `λ`. For each `z`, `eqv(z) - χ(z)` lies in `ker(chiA χ)`, the
  preimage of `Q` in `imA n`. So `γ(z) - χ(z) ∈ Q` vanishes at `λ`, i.e. `γ(z)(λ) = χ(z)`.
* `fib_finite`: for each coordinate `a`, `X_a` satisfies a monic equation `p` over `imA n`.
  Applying `chiA χ` to its coefficients gives a nonzero polynomial `q_a` over `ℂ` with
  `q_a(λ_a) = 0` for every `λ ∈ fib n χ` (`Polynomial.hom_eval₂`, `chiA_eval`). So `fib n χ` lies
  in the finite product of the root sets of the `q_a`.
* Height. `hgt n x = -Σ_r r · Re(x_r)` (`hgt_add`, `hgt_sub`, `hgt_single`). A positive root
  `e_p - e_q` with `p < q` has height `q - p ≥ 1`. So `cone_hgt`: every `v ∈ Q₊`
  (`VermaGL.posRootCone`) is `0` or has height `≥ 1` (induction over the additive closure).
* `lowerVermaCentral`: choose `λ ∈ fib n χ` of minimal height (`Set.exists_min_image`, using
  `fib_finite` and `fib_nonempty`). Then `z • gen λ = γ(z)(λ) • gen λ = χ(z) • gen λ`. If
  `λ - μ ∈ Q₊` and `μ ≠ λ`, then `hgt μ ≤ hgt λ - 1 < hgt λ`, so `μ ∉ fib n χ`. Hence some `z`
  has `γ(z)(μ) ≠ χ(z)`. With `c = χ(z)`, `z • gen λ = c • gen λ`. And `z • gen μ = γ(z)(μ) • gen μ`
  differs from `c • gen μ` because `gen μ ≠ 0` (`gen_ne_zero`, `smul_left_injective`).
