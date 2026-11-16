# The Whittaker sums along a column

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionGSide`. This is a helper
module for half (E) of the Whittaker expansion. It is internal to this proof and not taken from
the literature, though the computation is the standard one behind the Piatetski-Shapiro–Shalika
expansion. It covers the "G side": the partial Whittaker sums
`G_j(x) = Σ_{q ∈ N_j(F) \ GL_j(F)} W_f(diag(q, I) x)`. It proves the properties of these sums
that the uniqueness lemma `eq_zero_of_colCoeffB_eq_zero` (module `ColumnsB`) needs.

Notation. `F` is a number field, `ψ` is an additive character of `𝔸_F`, and
`f : GL_(r+1)(𝔸_F) → ℂ` is a function on the group-scheme points (`Points F (r + 1)`).
`W_f = whittaker F r ψ f` is the library Whittaker function of `f`, and
`padRational F hk q = diag(q, I)`.

## Character series on the torus (namespace `Langlands.Automorphic.CuspidalWhittaker`)

For a family of rational vectors `a_q ∈ K^Idx` and weights `w_q` with `Σ ‖w_q‖ < ∞`:

* `continuous_tsum_pairingCharacter`: `y ↦ Σ_q ψ₀(a_q · y) w_q` is continuous. This is uniform
  convergence (`continuous_tsum`), since each character has norm `1`.
* `isPeriodic_tsum_pairingCharacter`: the series is `K^Idx`-periodic, term by term.
* `torusIntegral_pairingCharacter_mul_conj`: on the torus `(𝔸_K/K)^Idx`,
  `∫ ψ₀(a · y) conj ψ₀(a₀ · y) dy` is `1` if `a = a₀` and `0` otherwise. The product is the
  character of `a − a₀`. The nontrivial case is the library
  `Unfolding.torusIntegral_pairingCharacter`.
* `fourierCoeff_tsum_pairingCharacter` (`Q` countable): the Fourier coefficient of the series at
  `a₀` is `Σ_q [a_q = a₀] w_q`. The proof integrates term by term
  (`integral_tsum_of_summable_integral_norm`, using that the torus measure is a probability
  measure) and then applies orthogonality.

## Block matrices

* `topBlock hk M`: the upper left `k × k` block of an `n × n` matrix.
* `topBlock_mul`: `topBlock (M N) = topBlock M · topBlock N` when `M` is a block matrix of size
  `k` (`IsBlk k M`: `M` agrees with the identity outside the upper left `k × k` block).
  `topBlock_one` handles the identity.
* `topBlockGL hk g hg`: the upper left block of an invertible block matrix, as an element of
  `GL_k(R)`. Its inverse is the block of `g⁻¹`, which is again a block matrix (`IsBlk.inv`).
* `padGL_topBlockGL`: `diag(topBlockGL g, I) = g`.

## Cosets and the sums (namespace `Langlands.Global.RankinSelbergGlobal.Unfolding`)

* `cosetMulRight F A`: right multiplication `N_k(F) g ↦ N_k(F) g A` for `A ∈ GL_k(F)`, as a
  bijection of `UnipotentRationalCosets F k`. `rightRel_cosetMulRight` relates the chosen
  representatives.
* `whittakerSum F ψ f j hj x = Σ'_{q ∈ N_j(F) \ GL_j(F)} W_f(diag(q.out, I) x)` for
  `j ≤ r + 1`. This is `G_j`.
* `whittakerSumGL F ψ f j hj g`: the same sum as a function on the library matrix group
  `AdelicGL F (r + 1)`. It is `G_j ∘ adelicHomeomorph.symm`. This is `G̃_j`.
* `rowChar F b q : Fin (r + 1) → F`: `b` times the last row of `q.out ∈ GL_(j+1)(F)`, padded
  with zeros.

## Results

* `rowChar_castLE`: entry `c ≤ j` of `rowChar F b q` is `b · q.out(j, c)`.
* `rowChar_ne_zero`: if `b ≠ 0`, then `rowChar F b q ≠ 0`, because the last row of an
  invertible matrix is nonzero (`lastRow_ne_zero`).
* `castLE_eq_charIdx_iff`: `c` and `charIdx j` are the same index exactly when `c` is the last
  index `j`.
* `rowChar_eq_single_iff`: for `b ≠ 0`, `rowChar F b q = b e_j` exactly when the last row of
  `q.out` is the standard row `e_j` (`LastRowStandard`).
* `symm_colUnit_mul`: pulled back to the group-scheme points, the library column matrix
  `colUnit (j+1) y` is the column point `colPoint F y`.
* `symm_rational_mul_of_isBlk`: pulled back to the group-scheme points, left multiplication by
  a rational block matrix `β` of size `k` is left multiplication by
  `diag(topBlockGL β, I)`.

Assume from here on that `ψ` is a standard character and `f` is left invariant under
`GL_(r+1)(F)`.

* `whittaker_padRational_colPoint_eq`: assume `ψ = ψ₀(b ·)` with `ψ₀ = standardCharacter F`.
  Then `W_f(diag(q, I) u_(j+1)(y) x) = ψ₀(rowChar F b q · y) W_f(diag(q, I) x)` for
  `q ∈ GL_(j+1)(F)` and `j < r`. This follows from the library
  `whittaker_padRational_colPoint`, after truncating `y` to its first `j + 1` coordinates
  (`colPoint_truncVec`).
* `whittaker_padRational_cosetPad`: `W_f(diag(cosetPad q, I) x) = W_f(diag(q, I) x)`. Here
  `cosetPad` embeds `N_j \ GL_j` into `N_(j+1) \ GL_(j+1)` by `q ↦ diag(q, 1)`.
* `whittakerSum_padRational_mul`: `G_k(diag(A, I) x) = G_k(x)` for `A ∈ GL_k(F)`. Each term
  becomes the term at the coset `q A`. Then reindex along `cosetMulRight F A`. No summability is
  needed, because a bijection preserves `tsum`.
* `whittakerSumGL_rational_mul`: the same invariance for `G̃_k` and rational block matrices of
  size `k`.
* `whittakerSum_zero`: `G_0 = W_f`. The group `GL_0(F)` is trivial. This lemma needs neither
  hypothesis on `ψ` and `f`.

Column section. Assume `ψ = ψ₀(b ·)`, `j < r`, and absolute summability of
`q ↦ W_f(diag(q, I) x)` over `N_(j+1) \ GL_(j+1)` for every `x` (`hsum`).

* `whittakerSumGL_colUnit_mul`: `G̃_(j+1)(u_(j+1)(y) g)` is the character series
  `Σ_q ψ₀(rowChar F b q · y) W_f(diag(q, I) x)` with `x = adelicHomeomorph.symm g`.
  This lemma does not use `hsum`.
* `continuous_whittakerSumGL_col`, `isPeriodic_whittakerSumGL_col`: continuity (uses `hsum`)
  and periodicity along the column.
* `fourierCoeff_whittakerSumGL_col` (with `𝔸_F/F` compact): the Fourier coefficient along the
  column at `a₀` is `Σ_q [rowChar F b q = a₀] W_f(diag(q, I) x)`.
* `fourierCoeff_zero_whittakerSumGL_col`: for `b ≠ 0` the zeroth coefficient vanishes, because no
  `rowChar` is zero.
* `colCoeffB_whittakerSumGL` (step identity): for `b ≠ 0`,
  `colCoeffB hj b G̃_(j+1) = G̃_j`. The coefficient at `b e_j` keeps exactly the cosets whose
  last row is `e_j` (`rowChar_eq_single_iff`). These are the image of the injective map
  `cosetPad` (`lastRowStandard_out_iff`). Reindex along it (`Function.Injective.tsum_eq`) and
  apply `whittaker_padRational_cosetPad`.
