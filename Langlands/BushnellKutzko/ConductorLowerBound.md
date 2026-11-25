# The lower bound for the functional-equation exponent

## Setting

As in `ConductorUpperBound`: `K` is a `p`-adic field with canonical order `T.ord`
(`T = K.canonicalTopologicalData`), `N = n + 1`, `GL_N(K)` carries the Library Haar measure,
`ψ` is a `UnitaryAdditiveCharacter K.Carrier`, `ν` an `AdditiveHaarMeasure K.Carrier` with
`SigmaFinite ν.measure`, and `σ` a complex representation of `GL_N(K)` with
`GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a` (both Euler
polynomials `1`, unit `c`, exponent `a`). `𝓛` is a lattice chain in `K^N` with period
`e = 𝓛.period`, `𝔓^j(𝓛) = 𝓛.endFiltration j`, and `U^k(𝔄(𝓛)) = unitSubgroup K 𝓛 k`. For
`g ∈ GL_N(K)`, `g^{-T}` is `GeneralLinear.inverseTranspose (n + 1) K.Carrier g`. For a set
`C ⊆ GL_N(K)`, the Library set `GodementJacquet.scalarSaturation C` is
`{z c | z ∈ K^×, c ∈ C}` (scalar matrices `z`). `SmoothDual σ` is the space of smooth linear
functionals on `V` and `smoothContragredient σ` the contragredient action on it.

## Declarations

General lemmas, for a field `F`:

- `toLin'_list_prod`: `toLin'` of a product of a list of matrices is the product of the `toLin'`.
- `val_inv_inverseTranspose`: the matrix of `(g^{-T})⁻¹` is `gᵀ`.
- `pow_smul_inv_prod_inverseTranspose`: for `t ∈ F` and a list `g₁, …, g_m` in `GL_N(F)`,
  `t^{-m} (g₁^{-T} ⋯ g_m^{-T})⁻¹ = (t⁻¹ g_mᵀ) ⋯ (t⁻¹ g₁ᵀ)` as matrices.
- `val_scalar_mul`: the matrix of `scalar z * c` is `z • c`.

Over the `p`-adic field `K`:

- `ord_det_list_prod`: if every matrix in a list has nonzero determinant of order `μ`, the
  product has nonzero determinant of order `m μ`, `m` the length of the list.
- `smoothContragredient_inv_apply`: `(smoothContragredient σ h⁻¹ ℓ)(v) = ℓ(σ(h) v)`.
- `exists_list_of_stratum` (iterating the shell): assume the functional-equation data, `k ≥ 1`,
  a smooth vector `w` with `σ(g) w = ψ(tr(b'(g - 1))) w` for all `g ∈ U^k(𝔄(𝓛))`, a smooth
  functional `ℓ` with `ℓ(w) ≠ 0`, `t ≠ 0` with `x ↦ ψ(t x)` nontrivial on `𝔬_K`, and
  `t⁻¹ b' ∈ 𝔓^{-k}(𝓛)`. Then for every `m` there is a list `g₁, …, g_m` in `GL_N(K)` with
  `ord(det gᵢ) = -a` and `t⁻¹ (gᵢᵀ - b') ∈ 𝔓^{1-k}(𝓛)` for each `i`, and
  `ℓ(σ(g₁^{-T} ⋯ g_m^{-T}) w) ≠ 0`.
- `le_period_mul_of_stratum` (the lower bound): under the hypotheses of `exists_list_of_stratum`,
  assume moreover
  - `hpow`: for every `i`, `(t⁻¹ b')^i ∉ 𝔓^{1-ik}(𝓛)`, and
  - `hsupp`: there is a compact set `C ⊆ GL_N(K)` such that `ℓ(σ(h) w) ≠ 0` implies
    `h ∈ scalarSaturation C`.

  Then `N k - e N ord(t) ≤ e a`.
- `period_mul_eq_of_stratum` (the exponent): under the hypotheses of `le_period_mul_of_stratum`,
  `e a = N k - e N ord(t)`.

When `ψ` is trivial on `𝔬_K` but not on `𝔭_K^{-1}`, take `t = ϖ⁻¹` for a uniformizer `ϖ`. Then
`ord(t) = -1`, and `ψ₁(x) = ψ(t x)` is trivial on `𝔭_K` but not on `𝔬_K`. The equality reads
`e a = N (k + e)`, that is `a = N (1 + k/e)`. In the proof of T2, `[𝔄(𝓛), k, k - 1, b]` is a
stratum contained in `σ`, with respect to `ψ₁`, that attains the normalized level `k/e`, and
`b' = ϖ⁻¹ b`, so that `ψ₁(tr(b (g - 1))) = ψ(tr(b' (g - 1)))` and `t⁻¹ b' = b`. Then `hpow` is
`pow_add_not_mem_of_isNormalizedLevel` (module `LevelAttainingStratum`) with `y = 0`, and
`hsupp` holds for supercuspidal `σ` by the Library theorem
`GodementJacquet.exists_centralCharacter_compactScalarSupport`.

## Provenance

This module proves the lower bound in the determinant-shell derivation of the exponent
formula `a = N (1 + m/e)` from Bushnell (1987), Theorem 3, and Bushnell–Fröhlich (1985),
(3.3.8). The bound is internal to T2. The proof iterates the shell identity and uses
compact support modulo the centre and the growth estimate of `CompactLevelBound`.

## Proof

`toLin'_list_prod`, `ord_det_list_prod` and `pow_smul_inv_prod_inverseTranspose` are inductions
on the list. The last one uses `(x y)⁻¹ = y⁻¹ x⁻¹`, `val_inv_inverseTranspose` and
`(s • A)(s' • B) = (s s') • (A B)`. `val_scalar_mul` is an entrywise computation.
`smoothContragredient_inv_apply` unfolds the contragredient as the transpose of `σ((h⁻¹)⁻¹)`.

`exists_list_of_stratum`: induction on `m`, starting from the empty list (`ℓ(w) ≠ 0`). Given a
list with product `P = g₁^{-T} ⋯ g_m^{-T}` and `ℓ(σ(P) w) ≠ 0`, the translated functional
`ℓ' = smoothContragredient σ P⁻¹ ℓ` satisfies `ℓ'(w) = ℓ(σ(P) w) ≠ 0`. Apply
`exists_ord_det_eq_of_stratum` (module `ConductorUpperBound`, with `j = -k ≤ 1 - k`) to `ℓ'`.
This gives `g` with `ord(det g) = -a`, `t⁻¹ (gᵀ - b') ∈ 𝔓^{1-k}(𝓛)` and
`ℓ(σ(P g^{-T}) w) = ℓ'(σ(g^{-T}) w) ≠ 0`. Append `g` to the list.

`le_period_mul_of_stratum`: choose a uniformizer `ϖ` and apply the growth bound
`LatticeChain.period_mul_le_of_forall_exists` (module `CompactLevelBound`) to the compact set
`C⁻¹`, with `j = -k` and `μ = -a - N ord(t)`. For each `m` it asks for `c ∈ C⁻¹` and a nonzero
scalar `s` with `s c ∉ 𝔓^{1-mk}(𝓛)` and `ord(det(s c)) = m μ` (order taken with `ordOf ϖ`). Take the list `g₁, …, g_m` of
`exists_list_of_stratum`. By `hsupp`, `P = g₁^{-T} ⋯ g_m^{-T} = z c₀` with `z` scalar and
`c₀ ∈ C`. Put `c = c₀⁻¹` and `s = t^{-m} z⁻¹`. By `pow_smul_inv_prod_inverseTranspose` and
`val_scalar_mul`, `s c` is the product `X_m ⋯ X_1` with `X_i = t⁻¹ gᵢᵀ`.

- Each `X_i` lies in `t⁻¹ b' + 𝔓^{1-k}(𝓛)`, so with `hb` and `hpow`,
  `LatticeChain.list_prod_not_mem` (module `CompactLevelBound`) gives
  `X_m ⋯ X_1 ∉ 𝔓^{1-mk}(𝓛)`.
- Each `X_i` has `ord(det X_i) = -a - N ord(t)` (`ord_det_inv_smul_transpose`), so the product
  has order `m μ` (`ord_det_list_prod`, `ordOf_eq_ord`).

The growth bound then gives `e (-a - N ord(t)) ≤ -N k`, which rearranges to the claim.

`period_mul_eq_of_stratum`: combine `le_period_mul_of_stratum` with `period_mul_le_of_stratum`
(module `ConductorUpperBound`, with `j = -k`).
