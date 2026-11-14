# Weyl representatives for the parahoric cells

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
shows that a parahoric-invariant vector of the principal series of rank `n + 2` is
determined by its values at the `n + 2` permutation matrices `w_j`. The definitions
are internal auxiliary constructions, with no literature source. All declarations
are in `Langlands.Conductor.SphericalCyclicity`. The notation is from
[`Cells`](Cells.md) and [`Parahoric`](Parahoric.md). `J = parahoric ϖ`,
`K = integralSubgroup 𝒪 (n + 1)` and `t' = tPrime ϖ`.

## Weyl representatives

- `weyl j`, written `w_j`, is the permutation matrix
  `(Equiv.swap 0 j).permMatrix F` of the transposition `(0 j)`, as an invertible
  matrix.
- `weyl_val` and `weyl_apply`: row `r` of `w_j` is the unit vector at `swap 0 j r`.
  `weyl_mul_val`: `w_j M = M.submatrix (swap 0 j) id`, so left multiplication
  permutes rows.
- `weyl_mul_self`: `w_j w_j = 1`. `weyl_zero`: `w_0 = 1`. `weyl_mem_integral`:
  `w_j ∈ K`.
- `tPrime_val_eq`: `t' = diagonal (i ↦ if i = 0 then 1 else ϖ)`.
- `lamJ j i = [i ≠ j]` is an exponent vector, with `lamJ_self` and `lamJ_of_ne`.
  `weyl_mul_tPrime`: `w_j t' = τ_j w_j`, where `τ_j = Iwasawa.torus ϖ (lamJ j)` is the
  diagonal matrix with `1` at `j` and `ϖ` elsewhere.

## The normalized character at `τ_j`

- `normalizedCharacter_torusBorel`: at the torus element `torusBorel m ϖ lam`, the
  normalized character is `Spherical.halfModulus q lam · Π z_i^(lam i)`. This
  compares the Library's `sphericalSection_torus` with
  `sphericalSection_borel_mul_integral` at the identity.
- `sum_weight_eq_zero`: `Σ_{i < n+2} (n + 1 - 2i) = 0`. `weight_lamJ`: the
  half-modulus exponent of `lamJ j` is `n + 1 - 2j`. `prod_lamJ`:
  `(Π_i z_i^(lamJ j i)) z_j = Π_i z_i`.
- `normalizedCharacter_lamJ`: `χ_z(τ_j) · z_j q^j = √q^(n+1) Π_i z_i`, which does not
  depend on `j`. Write `s = √q`. Then `s^(n+1-2j) q^j = s^(n+1)`, since `s² = q`.

## The cell lemma

- `IsParahoricInvariant f` means `f (g k) = f g` for all `k ∈ J` and all `g`.
- `unipGL β m hβ` is the unipotent matrix `1 + β e_mᵀ` for a vector `β` with
  `β m = 0`. Its inverse is `1 - β e_mᵀ` (`clearMat_mul_self`). It is upper
  triangular when `β` vanishes from `m` on (`unipGL_mem_borel`), and integral when
  `β` is (`unipGL_mem_integral`). `unipGL_mul_apply_zero`:
  `(u κ)_(r,0) = κ_(r,0) + β_r κ_(m,0)`.
- `clearVec κ m` is the vector with entries `-κ_(i,0)/κ_(m,0)` for `i < m`, and `0`
  otherwise.
- `value_eq_weyl` (cell lemma): let `f` be parahoric invariant and `κ ∈ K`, and let
  `m` be a row with `v(κ_(m,0)) = 1` and `v(κ_(i,0)) < 1` for every `i > m`. Then
  `f(κ) = f(w_m)`. Proof: `u = unipGL (clearVec κ m) m` is integral and upper
  triangular, so the normalized character is `1` at `u`
  (`normalizedCharacter_eq_one_of_integral`), and `f(κ) = f(u κ)`. The first column
  of `u κ` vanishes above row `m` and agrees with that of `κ` from row `m` on. Hence
  `w_m u κ` has first-column tail of valuation `< 1`, so it lies in `J`. Then
  `f(u κ) = f(w_m (w_m u κ)) = f(w_m)`.
- `eq_of_weyl`: two parahoric-invariant `f` and `g` that agree at every `w_j` are
  equal. Proof: by Iwasawa (`exists_borel_integral`), `x = b k` with `k ∈ K`, and
  covariance reduces to `f(k) = g(k)`. Some entry of the first column of `k` has
  valuation `1`. Otherwise `det k` would be congruent to `k_00 det(low k)` modulo the
  maximal ideal (`val_det_sub_head_mul_lt`), with `v(k_00) < 1`, which contradicts
  `v(det k) = 1`. Let `m` be the last such row. The cell lemma gives `f(k) = f(w_m)`
  and `g(k) = g(w_m)`.
