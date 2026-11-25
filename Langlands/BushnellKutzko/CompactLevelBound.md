# Products in a coset and a determinant bound on compact sets

Module `Langlands.BushnellKutzko.CompactLevelBound`. It imports
`Langlands.BushnellKutzko.LevelAttainingStratum`. It supplies the filtration and
determinant estimates used in the lower bound for the conductor. These estimates concern
products of endomorphisms and compact sets of invertible matrices.

Throughout, `F` is a nonarchimedean local field with a uniformizer `ϖ` (`hϖ : Irreducible ϖ`),
`ord = ordOf hϖ` is the valuation normalized by `ϖ`, `ι` is a finite type, `N = Fintype.card ι`,
`𝓛` is an `𝔬_F`-lattice chain in `F^ι` with period `e = 𝓛.period`, and
`𝔓^j(𝓛) = 𝓛.endFiltration j`. A matrix `M` acts on `F^ι` as `Matrix.toLin' M`.

## Main results

1. **Products** (`LatticeChain.list_prod_sub_pow_mem 𝓛 hb l hl`). Let `b ∈ 𝔓^j(𝓛)` and let `l`
   be a list of endomorphisms, each in `b + 𝔓^{j+1}(𝓛)`. With `k` the length of `l`, the
   product satisfies `l.prod - b^k ∈ 𝔓^{kj+1}(𝓛)`. The corollary
   `LatticeChain.list_prod_not_mem 𝓛 hb hpow l hl` adds the hypothesis that `b^k ∉ 𝔓^{kj+1}(𝓛)`
   for every `k`. It concludes that `l.prod ∉ 𝔓^{kj+1}(𝓛)`. With `j = -m`, the hypothesis
   `hpow` is the case `y = 0` of `pow_add_not_mem_of_isNormalizedLevel`.
2. **Determinant bound** (`LatticeChain.card_mul_le_period_mul_ordOf_det 𝓛 hϖ hX hdet`). If
   `X ∈ 𝔓^a(𝓛)` and `det X ≠ 0`, then `N a ≤ e · ord(det X)`.
3. **Compact sets modulo scalars** (`LatticeChain.exists_period_mul_ordOf_det_lt 𝓛 hϖ hC`). Let
   `C` be a compact subset of `GL(ι, F) = Matrix.GeneralLinearGroup ι F`, with the topology of
   units of the matrix ring. There is `B ∈ ℤ` such that, for all `g ∈ C`, all `a ∈ F`, `a ≠ 0`,
   and all `j ∈ ℤ`: if `a g ∉ 𝔓^j(𝓛)`, then `e · ord(det(a g)) < N j + B`.
4. **Growth bound** (`LatticeChain.period_mul_le_of_forall_exists 𝓛 hϖ hC h`). Let `C` be as
   in 3 and `j, μ ∈ ℤ`. Suppose that for every `n ∈ ℕ` there are `g ∈ C` and `a ≠ 0` with
   `a g ∉ 𝔓^{nj+1}(𝓛)` and `ord(det(a g)) = n μ`. Then `e μ ≤ N j`.

In the T2 lower bound (module `ConductorLowerBound`), `C` comes from the compact support modulo the centre of a
coefficient of a supercuspidal representation (Library
`GodementJacquet.exists_centralCharacter_compactScalarSupport`). The products `a g` are
products of `n` elements of `b + 𝔓^{1-f}(𝓛)` whose determinants all have the same valuation.
Result 4 then gives the inequality between the Godement–Jacquet exponent and `N f / e`.

## Provenance

These are standard facts, used here as internal steps; they are not results of Bushnell (1987),
whose lower bound goes through his Theorem 4 instead. Result 2 is the lattice-chain form of the
estimate `|det x| ≤ q^{-N a / e}` for `x ∈ 𝔓^a`, which holds because `𝔓^{e a} = ϖ^a 𝔄` and
elements of `𝔄` have integral determinant (compare BK93 (1.1.2), printed p. 20, for
`𝔓^j(𝓛) = End^j_𝔬(𝓛)`). Result 3 expresses that a compact subset of `GL_N(F)` is bounded and
has bounded determinant valuations.

## Proof as implemented

1. **Products.** Induction on the list, with
   `x · P - b · b^k = (x - b) · P + b · (P - b^k)` for `P = l.prod`. Here `P ∈ 𝔓^{kj}(𝓛)`
   because `P = b^k + (P - b^k)` and `b^k ∈ 𝔓^{kj}(𝓛)` (`pow_mem_endFiltration_natMul`). Both terms
   lie in `𝔓^{(k+1)j+1}(𝓛)` by `mul_mem_endFiltration`. The corollary subtracts:
   `b^k = P - (P - b^k)`.
2. **Scalars.** `integer_smul_mem_endFiltration`: an integral scalar preserves `𝔓^j(𝓛)`.
   `smul_mem_endFiltration_ordOf`: for `c ≠ 0`, `c Y ∈ 𝔓^{j + e ord(c)}(𝓛)` if `Y ∈ 𝔓^j(𝓛)`, by
   `smul_mem_iff` for vectors. `ordOf_pow`: `ord(c^k) = k ord(c)`.
3. **Integral determinants** (`det_mem_integer_of_mem_endFiltration_zero`). Take an
   `𝔬_F`-basis of `L_0` (`Module.finBasis`) and the `F`-basis of `F^ι` that it defines
   (`Module.Basis.extendOfIsLattice`). The matrix of `Y ∈ 𝔓^0(𝓛)` in this basis has integral
   entries (`repr_extendOfIsLattice_mem`), so its determinant is the image of the determinant
   of a matrix over `𝔬_F` (`RingHom.map_det`).
4. **Determinant bound.** For `X ∈ 𝔓^a(𝓛)`: `X^e ∈ 𝔓^{ea}(𝓛)`, so `ϖ^{-a} X^e ∈ 𝔓^0(𝓛)` by
   step 2. Its determinant `ϖ^{-aN} (det X)^e` is integral by step 3. Taking `ord` gives
   `0 ≤ -aN + e ord(det X)`.
5. **Bounded entries** (`exists_pow_mul_mem_of_isCompact`,
   `exists_pow_mul_entry_mem_of_isCompact`). The sets `{x : ϖ^s x ∈ 𝔬_F}`, `s ∈ ℕ`, are open
   (`Valuation.isOpen_integer`), increasing, and cover `F`. A compact set lies in one of them
   (`IsCompact.elim_directed_cover`). For a compact set of matrices, apply this to each entry
   and take the sum of the exponents.
6. **Bounded entries give a filtration bound** (`exists_mem_endFiltration`,
   `exists_forall_toLin'_mem_endFiltration`, `exists_forall_mem_endFiltration_of_isCompact`).
   Every endomorphism lies in some `𝔓^t(𝓛)`: expand it in elementary endomorphisms for a basis
   splitting `𝓛` (`exists_basis_splits_both`, `elementaryEnd_mem_iff`). Apply this to the
   matrix units `E_kl`. Then a matrix `M` with `ϖ^s M_kl ∈ 𝔬_F` is
   `Σ ϖ^{-s} (ϖ^s M_kl) E_kl` and lies in `𝔓^{t}(𝓛)` with `t = -Σ|t_kl| - e s`, by step 2.
7. **Compact sets modulo scalars.** By step 6 applied to `C` and to `C⁻¹`
   (`Units.continuous_val`, `Units.continuous_coe_inv`), all `g ∈ C` lie in `𝔓^t(𝓛)` and all
   `g⁻¹` in `𝔓^{t'}(𝓛)`. If `a g ∉ 𝔓^j(𝓛)`, then `j > t + e ord(a)` by step 2. Step 4 for
   `g⁻¹` gives `N t' ≤ -e ord(det g)`. With `det(a g) = a^N det g` (`Matrix.det_smul`),
   `e ord(det(a g)) = N e ord(a) + e ord(det g) ≤ N (j - t - 1) - N t' < N j + B` for
   `B = 1 - N (t + t')`.
8. **Growth bound.** Suppose `e μ > N j`. Take `n = (N + B).toNat` with `B` from step 7. Then
   `e n μ < N (n j + 1) + B`, so `n (e μ - N j) < N + B ≤ n`, contradicting `e μ - N j ≥ 1`.
