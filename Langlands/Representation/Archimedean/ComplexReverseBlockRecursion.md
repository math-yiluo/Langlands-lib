# Transposed matrix coefficients and the block Jacquet functional

Lean module: `Langlands.Representation.Archimedean.ComplexReverseBlockRecursion`, namespace
`Langlands.Archimedean.ComplexReverseBlockRecursion`. It is a helper for the Langlands-ordered case of
`ComplexReverseIntertwinerKernelStatement` (module `ComplexReverseIntertwinerTied`). It is the
analogue, for blocks of tied exponents, of `ComplexReverseRecursion` (the strictly ordered case).

## Notation

`GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with Haar probability
measure `unitaryHaar n`, and `gᵀ` is `ComplexReverseTwist.transposeGL g`. `IsPhasePower χ e` and
`dualChar χ` (the characters `z ↦ (χ_l z)⁻¹`, written `χ⁻¹`) come from `ComplexPartialJacquet`.

From the Library module `ComplexBlockJacquet` and `ComplexBlockLimit`: `blockDiagGL g₁ g₂ =
diag(g₁, g₂)`, `dTail s = diag(1_a, s·1_{k+1})`, `IsBlockDominant e a k` (the exponents
`e_a, …, e_{a+k}` have equal real part, the real parts of `e_0, …, e_{a-1}` are non-increasing and
`Re e_{a-1} > Re e_a`), `blockShiftChar k χ` (the characters `χ_l(z) (|z|²)^{-(k+1)/2}` of
`GL_a(ℂ)`), `blockStep h (g) = ∫ h(n̄(X) g) dX` (integral over the lower block unipotent of
`P_{a,k+1}`) and `blockPair φ h (g₁) = ∫_{U(k+1)} φ(κ₂) blockStep h (diag(g₁, κ₂)) dκ₂`.

From the module `ComplexBlockFunctional`: block decompositions `ks : List ℕ` (last block
first) with size `dim ks`, `BlockOrdered ks e` (each block tied, strict decrease between blocks:
`IsBlockDominant` at each cons), the block Jacquet functional `jac ks e p` (`jac [] e p h = h(1)`,
`jac (k :: ks) e p h = jac ks e' p (blockPair (blockVector (dim ks) k e p) h)` with
`e'_l = e_l - (k+1)/2`), and `TiedIrreducible` (every principal series of phase-power characters
with tied exponents is irreducible). From the module `ComplexBlockDual`:
`restrictBlock u (g₁) = u(diag(g₁, 1))` and `blockDualChar a χ`.

From the module `ComplexBlockLimitSum`: the leading term
`blockTerm u h = ∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`.

## Definitions

- `coeff x y g = ∫_{U(n)} x(κ g) y(κ) dκ`, written `M_{x,y}(g)`.
- `IsOrthStable n χ y`: there is a nonzero space `V` of `U(n)`-finite functions of the principal
  series of `χ⁻¹`, stable under right translation by `U(n)` and under all right derivatives
  `rightDerivative X`, with `∫_{U(n)} v y = 0` for every `v ∈ V`.
- `HasTransposeExpansion n χ x y`: there are a finite type `ι` and functions `α_i` (`U(n)`-finite,
  principal series of `χ⁻¹`) and `β_i` (`U(n)`-finite, principal series of `χ`), each `β_i`
  satisfying `IsOrthStable n χ`, with `M_{x,y}(g) = ∑_i M_{α_i,β_i}(gᵀ)` for every `g ∈ GL_n(ℂ)`.

## Results

- `transposeGL_one`, `transposeGL_blockDiagGL` (`diag(g₁, g₂)ᵀ = diag(g₁ᵀ, g₂ᵀ)`),
  `transposeGL_dTail` (`d(s)ᵀ = d(s)`).
- `blockTerm_neg`: `blockTerm (-u) h = -blockTerm u h`.
- `blockTerm_eq_sum_of_ray`. Assume `ComplexBlockChartIntegrableStatement`,
  `ComplexBlockParabolicIntegrationStatement`, `IsPhasePower χ e` and `IsBlockDominant e a k`.
  Let `u₀`, `u_i` (finitely many) lie in the principal series of `χ⁻¹` and `h₀`, `h_i` in that of
  `χ`. If `∫ u₀(κ d(s)) h₀(κ) dκ = ∑_i ∫ u_i(κ d(s)) h_i(κ) dκ` for every `s ∈ ℂˣ`, then
  `blockTerm u₀ h₀ = ∑_i blockTerm u_i h_i`.
- `blockTerm_translate_eq_of_product`. If `x'(diag(h₁, h₂)) = x(diag(h₁, 1)) φ(h₂)` for all
  `h₁, h₂`, then `blockTerm (x' ∘ R(diag(g₁, 1))) y = M_{restrictBlock x, blockPair φ y}(g₁)`.
- `blockTerm_translate_eq_sum`. Assume `ComplexBlockChartIntegrableStatement`, `IsPhasePower χ e`
  and `IsBlockDominant e a k`; let `β` be `U(a+k+1)`-finite in the principal series of `χ` and let
  `α(diag(h₁, h₂)) = ∑_j P_j(diag(h₁, 1)) S_j(h₂)` with continuous `P_j`, `S_j`. Then
  `blockTerm (α ∘ R(diag(g₁, 1))) β = ∑_j M_{restrictBlock P_j, blockPair S_j β}(g₁)`.
- `mul_jac_eq_zero` (main result). Assume `ComplexBlockChartIntegrableStatement`,
  `ComplexBlockParabolicIntegrationStatement` and `TiedIrreducible`. Let `ks` be a block
  decomposition, `IsPhasePower χ e`, `χ_l` on the unit circle equal to `z ↦ z^{p_l}`, and
  `BlockOrdered ks e`. Let `U` be a space of `U(n)`-finite functions of the principal series of
  `χ⁻¹` (`n = dim ks`), stable under right translation by `U(n)` and under right derivatives, and
  `y` a `U(n)`-finite function of the principal series of `χ`. If `HasTransposeExpansion n χ x y`
  for every `x ∈ U`, then `x(1) · jac ks e p y = 0` for every `x ∈ U`.

## Proof

- The transposition lemmas are entrywise (`Matrix.fromBlocks_transpose`,
  `Matrix.diagonal_transpose`).
- `blockTerm_eq_sum_of_ray` applies `sum_blockTerm_eq_zero` (`ComplexBlockLimitSum`) to the family indexed by
  `Option ι`: `(u₀, h₀)` at `none` and `(-u_i, h_i)` at `some i`. The hypothesis makes the ray sums
  vanish, and `blockTerm_neg` turns the conclusion into the claimed identity.
- `blockTerm_translate_eq_of_product` and `blockTerm_translate_eq_sum` unfold `blockTerm`,
  `blockPair` and `blockStep`, use `diag(κ₁, κ₂) diag(g₁, 1) = diag(κ₁ g₁, κ₂)` and exchange the
  finite sum with the `U(a)`- and `U(k+1)`-integrals. Integrability comes from continuity on the
  compact groups (`integrable_of_continuous_unitary`, `continuous_blockStep`, `blockPair_mem`).
- `mul_jac_eq_zero`, by induction on `ks`.
  - `ks = []`: `GL_0(ℂ)` is trivial, so `M_{x,y}(g) = x(1) y(1)`. For each `β_i` choose a nonzero
    `v` in its orthogonal stable space; then `v(1) ≠ 0` and `v(1) β_i(1) = 0`, so `β_i(1) = 0`.
    Evaluating the expansion at `g = 1` gives `x(1) y(1) = 0`, and `jac [] e p y = y(1)`.
  - `ks = k :: ks'`, `a = dim ks'`. `TiedIrreducible` applies to the characters
    `blockDualChar a χ` of the tied last block (`isPhasePower_blockDualChar`,
    `blockDualChar_phase`, the tie condition of `IsBlockDominant`), so this principal series of
    `GL_{k+1}(ℂ)` is irreducible. If `U = 0` the claim is trivial. Otherwise the restricted space
    `U' = restrictBlock(U)` is a nonzero stable space of `U(a)`-finite functions of the principal
    series of `(blockShiftChar k χ)⁻¹` (`map_restrictBlock`), and
    `y' = blockPair (blockVector a k e p) y` is `U(a)`-finite in the principal series of
    `blockShiftChar k χ` (`blockPair_mem`, `blockVector_mem`).

    Every element of `U'` has a transposed expansion against `y'`. Write it as `restrictBlock x`
    with `x ∈ U`. By `exists_mem_blockDiag_eq` (`ComplexBlockSlice`; this uses the
    irreducibility above) there is `x'' ∈ U` with
    `x''(diag(h₁, h₂)) = x(diag(h₁, 1)) φ(h₂)` for `φ = blockVector a k e p`. Take the expansion
    `M_{x'',y}(g) = ∑_i M_{α_i,β_i}(gᵀ)` and decompose each `α_i` by `exists_blockDiag_decomposition`
    (`ComplexBlockSlice`): `α_i(diag(h₁, h₂)) = ∑_j P_{ij}(diag(h₁, 1)) S_{ij}(h₂)`. Evaluating the
    expansion at `d(s) diag(g₁, 1)` and using `(d(s) diag(g₁, 1))ᵀ = d(s) diag(g₁ᵀ, 1)` gives the
    ray identity for the translates `R(diag(g₁, 1)) x''` and `R(diag(g₁ᵀ, 1)) α_i`.
    `blockTerm_eq_sum_of_ray` then gives an identity of leading terms. By the two translate lemmas
    it reads `M_{restrictBlock x, y'}(g₁) = ∑_{i,j} M_{restrictBlock P_{ij}, blockPair S_{ij} β_i}(g₁ᵀ)`.
    The new right-hand functions are again orthogonal to nonzero stable spaces: for the space `V_i`
    of `β_i`, the restriction `restrictBlock(V_i)` is nonzero and stable (`map_restrictBlock`), and
    it is orthogonal to `blockPair S_{ij} β_i` by the dual step
    `integral_restrictBlock_mul_blockPair_eq_zero` of `ComplexBlockDual` (which uses the irreducibility above).

    The exponents shifted by `-(k+1)/2` are again `BlockOrdered` on `ks'` (`BlockOrdered.shift`),
    so the induction hypothesis applies to `U'` and `y'`. It gives
    `(restrictBlock x)(1) · jac ks' e' p y' = 0`, which is `x(1) · jac (k :: ks') e p y = 0`
    (`jac_cons`, `diag(1, 1) = 1`).

## Provenance

Derived (internal). This is the block version of the recursion `mul_jacquet_eq_of_transpose` in
`ComplexReverseRecursion`, in which the stepwise limit along `P_{n-1,1}` is replaced by the limit
along `P_{a,k+1}` for a block of tied exponents. The orthogonality invariant (`IsOrthStable`) and
the treatment of tied blocks follow the proof of the nonvanishing of the
block Jacquet functional on Langlands quotients (`ComplexBlockDual`, `ComplexBlockLanglandsQuotient`).
No statement from the literature is introduced; all results are proved here from the
listed modules.
