# Every level value carries a stratum (Bushnell 1987, Theorem 2′)

Lean proof by Worker 408 for Task 7683.

Module `Langlands.BushnellKutzko.StratumExistence`. It imports
`Langlands.BushnellKutzko.LevelAttainingStratum`, Mathlib's
`Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality` and
`Mathlib.NumberTheory.LegendreSymbol.AddCharacter`. It is an internal step of the proof of
T2 (Task 7683).

## Main results

Throughout, `K` is a `p`-adic field (`PadicField p`, with its canonical topology and valuation,
and the canonical topology on `GL_n(K)`). `ψ : AddChar K ℂ` is trivial on `𝔭_K` (`hψ`) but not on
`𝔬_K` (`hψ'`). Together these two hypotheses are the Library's `IsLevelOne K ψ`, stated here as
two separate hypotheses. `a` is a class of irreducible admissible complex representations of
`GL_n(K)` (`SmoothDualClass`).

1. `exists_containsStratum_of_hasFixedVector K n ψ hψ hψ' a 𝓛 hm hfix`. Let `𝓛` be an
   `𝔬_K`-lattice chain in `K^n` and `m ∈ ℕ` with `1 ≤ m` (`hm`). Assume `a` has a nonzero vector
   fixed by the image of `U^{m+1}(𝔄(𝓛))` in `GL_n(K)`
   (`hfix : SmoothDualClass.HasFixedVector (unitSubgroup K 𝓛 (m + 1)) a`). Then there is
   `b ∈ End_K(K^n)` with `ContainsStratum K n ψ a 𝓛 m b`. That is, `b ∈ 𝔓^{-m}(𝓛)`, and some
   representative of `a` has a nonzero vector `v` with `g v = ψ(tr(b(g - 1))) v` for all `g` in
   the image of `U^m(𝔄(𝓛))`.
2. `exists_containsStratum_of_isNormalizedLevel K n ψ hψ hψ' a hlev hx`. Assume
   `hlev : IsNormalizedLevel K n a x` (`x` is the least element of `normalizedLevelValues K n a`)
   and `hx : 0 < x`. Then there are a lattice chain `𝓛`, `m : ℕ` and `b` with
   - `x = m / e(𝓛)`, where `e(𝓛) = 𝓛.period`;
   - `ContainsStratum K n ψ a 𝓛 m b`, which includes `m ≥ 1`;
   - `b + y` is not nilpotent for every `y ∈ 𝔓^{1-m}(𝓛)`. That is, the stratum
     `[𝔄(𝓛), m, m - 1, b]` is fundamental in the sense of BK93 p. 57. The condition is stated
     inline, as in `LevelAttainingStratum`; no `Stratum` value is built.

## Provenance

- Result 1 is the first step in Bushnell (1987), *Hereditary orders, Gauss sums and supercuspidal
  representations of GL_N*, (3.3) and the proof of Theorem 2′, printed pp. 196–197. Bushnell
  uses that `U^m(𝔄)/U^{m+1}(𝔄)` is finite abelian, so a representation with a nonzero
  `U^{m+1}(𝔄)`-fixed vector contains a character of `U^m(𝔄)/U^{m+1}(𝔄)`. Each such character
  has the form `g ↦ ψ(tr(b(g - 1)))` with `b ∈ 𝔓^{-m}`.
- The description of these characters is BK93 (Bushnell–Kutzko, *The admissible dual of GL(N)
  via compact open subgroups*, 1993), (1.1.6), printed p. 22, in the case `r = n - 1`. Here it
  is `LatticeChain.exists_mem_endFiltration_forall_eq`, proved for `V = F^ι` with `ι` finite and a
  splitting basis.
- Result 2 combines result 1 with Bushnell's Theorem 2′(ii), proved here as
  `not_isNilpotent_of_isNormalizedLevel` (module `LevelAttainingStratum`). Bushnell states
  Theorem 2′ for minimal `f(𝔄, π)/e(𝔄)` over hereditary orders. Here the minimum is taken over
  lattice chains (`normalizedLevelValues`), and the hypothesis `0 < x` replaces Bushnell's
  assumption that every `f(𝔄', π)` is positive.
- The proof of the eigenvector step and of the matrix duality below works through
  residue coordinates and averaging over a finite abelian group. Bushnell and BK93 argue with
  the quotient group `U^m/U^{m+1}` and the duality (1.1.4)–(1.1.6) directly.

## Proof as implemented

Choose a uniformizer `ϖ` and a basis `β` splitting `𝓛` (`exists_basis_splits_both`, published
module `SplittingBasis`). Write `ν(β_k)` for `𝓛.index ϖ (β k)` and `E_kl(t)` for
`elementaryEnd β k l t` (published module `FiltrationCoordinates`).

1. **Characters of the residue field** (`exists_eq_addChar_mul`). Let `φ : 𝔬_F → ℂ` turn sums
   into products and be trivial on `𝔭_F`. Then `φ(s) = ψ(c s)` for some `c ∈ 𝔬_F`. Both `φ` and
   `s ↦ ψ(s)` descend to characters of the finite residue field `𝓀_F` (`residueAddChar`).
   The second is nontrivial by `hψ'`, hence primitive. So `c₀ ↦ ψ₀(c₀ ·)` is injective
   (`AddChar.to_mulShift_inj_of_isPrimitive`), hence bijective by counting (`AddChar.card_eq`).
   Lift the `c₀` with `ψ₀(c₀ ·) = φ₀` to `𝔬_F`.
2. **Coordinates of `𝔓^m(𝓛)`** (section `Coordinates`). Put
   `c_kl(m) = ⌈(m + ν(β_l) - ν(β_k)) / e⌉` (`coordExp`, via `coordShift e N = -((-N) / e)`).
   Then `E_kl(ϖ^{c_kl(m)} s) ∈ 𝔓^m(𝓛)` for `s ∈ 𝔬_F` (`elementaryEnd_coordExp_mem`). It lies in
   `𝔓^{m+1}(𝓛)` if `s ∈ 𝔭_F` (`..._mem_succ`), or if `e c_kl(m) ≠ m + ν(β_l) - ν(β_k)`, for every
   `s` (`..._mem_succ_of_ne`). Every `x ∈ 𝔓^m(𝓛)` has entries `x_kl = ϖ^{c_kl(m)} s_kl` with
   `s_kl ∈ 𝔬_F` (`exists_entry_eq_coordExp`, from `le_of_mem_endFiltration`).
3. **Matrix duality** (`LatticeChain.exists_mem_endFiltration_forall_eq`). Let `θ` turn sums of
   elements of `𝔓^m(𝓛)` into products and be trivial on `𝔓^{m+1}(𝓛)`. By step 1, for each `k, l`
   there is `a_kl ∈ 𝔬_F` with `θ(E_kl(ϖ^{c_kl} s)) = ψ(a_kl s)`. Let `b` have matrix entries
   `b_lk = a_kl ϖ^{-c_kl}` when `e c_kl = m + ν(β_l) - ν(β_k)`, and `0` otherwise. Then
   `b ∈ 𝔓^{-m}(𝓛)` by `elementaryEnd_mem_iff`. For `x ∈ 𝔓^m(𝓛)`, write `x` as the sum of the
   `E_kl(ϖ^{c_kl} s_kl)` and expand both sides as products (`fun_sum_eq_prod`,
   `addChar_sum_eq_prod`). The factor `ψ(tr(b E_kl(ϖ^{c_kl} s_kl))) = ψ(b_lk ϖ^{c_kl} s_kl)`
   (`trace_mul_elementaryEnd`) equals `θ(E_kl(ϖ^{c_kl} s_kl))`. If the exponent condition
   fails, both factors are `1` by step 2.
4. **Residue coordinates** (section `ResidueCoordinates`). Fix a lift `residueLift : 𝓀_F → 𝔬_F`.
   For `z : κ → κ → 𝓀_F` put `coordEnd z = ∑_{k,l} E_kl(ϖ^{c_kl(m)} z̃_kl) ∈ 𝔓^m(𝓛)`. Modulo
   `𝔓^{m+1}(𝓛)` this map is additive (`coordEnd_add_sub_mem`), sends `0` to `0`
   (`coordEnd_zero_mem`), and is onto `𝔓^m/𝔓^{m+1}` (`exists_sub_coordEnd_mem`).
5. **Units** (section `Units`). `U^j(𝔄)` is normalized by `U^0(𝔄)`
   (`inv_mul_mul_mem_unitFiltration`). If `g, h ∈ U^0(𝔄)` and `h - g ∈ 𝔓^j`, then
   `g⁻¹h ∈ U^j(𝔄)` (`inv_mul_mem_unitFiltration`).
6. **Common eigenvectors** (`exists_addChar_eigenvector`). Let `Q` be a finite abelian group and
   `T : Q → End_ℂ(V)` multiplicative on a `T`-stable subspace `W`. Then every nonzero `w ∈ W`
   gives a nonzero common eigenvector `v ∈ W`, `T z v = χ(z) v` for a character `χ` of `Q`. The
   vector is one of the averages `v_χ = ∑_z χ(-z) T z w`. They satisfy `T y v_χ = χ(y) v_χ`, and
   their sum over all `χ` is `|Q| w ≠ 0` (`AddChar.sum_apply_eq_ite`).
7. **Assembly** (`exists_containsStratum_of_hasFixedVector`). Take a representative `A` of `a`,
   `ρ` its representation, and `W` the subspace of `U^{m+1}(𝔄)`-fixed vectors (nonzero by `hfix`;
   `mem_fixedVectors_iff_forall_mem`). Transport units of `End(K^n)` to `GL_n(K)` by
   `Matrix.GeneralLinearGroup.toLin.symm`.
   - By step 5, units of `U^0(𝔄)` that agree modulo `𝔓^{m+1}` act identically on `W`. Also
     `U^0(𝔄)` preserves `W`.
   - For `z ∈ Q = (𝓀_F)^{κ×κ}` choose `f z ∈ U^m(𝔄)` with `f z = 1 + coordEnd z`
     (`exists_mem_unitFiltration`, using `m ≥ 1`). Since
     `(1 + X)(1 + Y) - (1 + Z) = (X + Y - Z) + XY` and `XY ∈ 𝔓^{2m} ⊆ 𝔓^{m+1}`,
     `T z = ρ(f z)` is multiplicative on `W` by step 4.
   - Step 6 gives `χ` and a nonzero `v ∈ W` with `ρ(f z) v = χ(z) v`. Then
     `θ(x) = χ(Z x)`, where `Z x` is a coordinate vector of `x ∈ 𝔓^m` (step 4), turns sums into
     products on `𝔓^m` and is trivial on `𝔓^{m+1}`. Step 3 gives `b ∈ 𝔓^{-m}(𝓛)` with
     `θ(x) = ψ(tr(b x))`.
   - For `g ∈ U^m(𝔄)`, `g` agrees with `f(Z(g - 1))` modulo `𝔓^{m+1}`, so
     `ρ(g) v = χ(Z(g - 1)) v = ψ(tr(b(g - 1))) v`. This is `ContainsStratum K n ψ a 𝓛 m b`.
8. **Theorem 2′** (`exists_containsStratum_of_isNormalizedLevel`). `hlev` gives `𝓛` and `m`
   with `x = m / e(𝓛)` and a nonzero `U^{m+1}(𝔄(𝓛))`-fixed vector; `x > 0` forces `m ≥ 1`.
   Step 7 gives `b`. Then `not_isNilpotent_of_isNormalizedLevel`, applied to the same `𝓛`, `m`,
   `b` and `hlev`, shows the stratum is fundamental.

## Other declarations

- `eq_of_sub_mem_maximalIdeal`, `residue_surjInv_sub_mem`, `residueAddChar`,
  `residueAddChar_residue`: the descent of step 1.
- `coordShift`, `le_mul_coordShift`, `mul_coordShift_lt`, `one_le_ordOf_of_mem_maximalIdeal`,
  `LatticeChain.period_pos'` (`0 < e` in `ℤ`), `LatticeChain.coordExp`, `le_mul_coordExp`,
  `mul_coordExp_lt`, `elementaryEnd_add`, `elementaryEnd_sub`: arithmetic for step 2.
- `residueLift`, `residue_residueLift`, `residueLift_add_sub_mem`, `residueLift_zero_mem`,
  `sub_residueLift_residue_mem`, `LatticeChain.coordEnd`, `coordEnd_mem`: step 4.
- The `p`-adic section declares the canonical instances as named local instances
  (`strExTopologicalSpace`, `strExValuativeRel`, `strExLocalField`, `strExTopologicalSpaceGL`),
  as in `LevelAttainingStratum` (compare Task 7696).
