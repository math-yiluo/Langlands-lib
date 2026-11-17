# Swapping two unlinked real characters

Module `Langlands.Representation.Archimedean.RealCharacterSwapProof` proves
`Langlands.Archimedean.RealCharacterSwapStatement` from the module
`Langlands.Representation.Archimedean.RealUnlinkedSwapReduction`. This is the `GL_2(ℝ)` case
(two character blocks) of the swap step in the proof of Speh's irreducibility criterion.
Mœglin (1997, §10, p. 165) reduces Theorem 10b to `GL_2`, `GL_3` and `GL_4`. For the
`GL_2(ℝ)` principal series, see Badulescu–Renard (2010), §9.2 and (9.1).

The proof uses only Library modules: `RealUnlinkedSwapReduction` (the target and
`realRank_perm`), `RealCharacterPairReducible` with `RealCharacterPairData` and
`RealBlockFrobeniusMap` (the Frobenius maps along the block of a pair of characters), and
`RealBlockMultiplierGeneric` (the generic multiplier without a condition on `Re ν`).

## Statement proved

`Langlands.Archimedean.RealCharacterSwap.realCharacterSwap : RealCharacterSwapStatement`.

Take `n : ℕ`, lists `pre post : List RealBlock` and real characters
`a = sgn^{ε_a} |·|^{s_a}` and `b = sgn^{ε_b} |·|^{s_b}`. Assume
`realRank (pre ++ character a :: character b :: post) = n`, `Re s_b ≤ Re s_a`, and that the
Mœglin data of `a` and `b` are not linked. Then there is an injective `ℂ`-linear map from the
`O(n)`-finite functions of the standard module of `pre ++ a :: b :: post` to those of
`pre ++ b :: a :: post`, and this map is an `IsRealStandardIntertwiner` into the second module.

The proof does not use the hypothesis `Re s_b ≤ Re s_a`. The map below is injective for every
unlinked pair, whatever the order of the real parts.

## Proof

### The injective generic swap (`exists_injective_swap`)

Let `c`, `d` be real characters, `ν = t_d - t_c` and `ε = pairParity c d = (ε_c + ε_d) mod 2`.
Assume `realRank (pre ++ c :: d :: post) = n`, and that `ν ≠ ε + 2m + 1` (`hne`) and
`ν ≠ -(ε + 2m + 1)` (`hden`) for every `m : ℕ`. Then
`RealInjectiveIntertwinerExists n (pre ++ d :: c :: post) (pre ++ c :: d :: post)`.

1. Let `μ = genericMultiplier ν ε`. Since `ε` is `0` or `1` (`pairParity_eq`), `μ` has the
   symmetry `IsSymmetric ε (sigma0 c d) μ` (`isSymmetric_genericMultiplier`), where
   `sigma0 c d = (-1)^ε`.
2. `RealCharacterPairReducible.data_swap` gives Frobenius data `h0` along the block at position
   `realRank pre`, from `pre ++ [d, c] ++ post` to `pre ++ c :: d :: post`, with multiplier `μ`.
   `RealCharacterPairReducible.data_unswap` gives Frobenius data `hB` in the other direction,
   with the pointwise inverse multiplier `k ↦ (μ k)⁻¹`.
3. `genericMultiplier_ne_zero_of_ne` (from `hne` and `hden`) shows that `μ k ≠ 0` for every
   `k : ℤ`.
4. At the first two positions of the block, the exponents of `pre ++ [d, c] ++ post` are `t_d` and
   `t_c` (`exponent_swp_zero`, `exponent_swp_one`). So the recurrence needed by
   `blockFrobMap_rightDerivative` is `IsRecurrent (ν + 1) ε μ`, and
   `isRecurrent_genericMultiplier_of_ne` gives it from `hden` alone.
5. **Intertwiner** (imported
   `RealBlockFrobeniusMap.isRealStandardIntertwiner_blockFrobMap`). For any Frobenius data with
   this recurrence, `blockFrobMap` is an `IsRealStandardIntertwiner` into the standard module of
   the target list. Membership in the `O(n)`-finite functions comes from
   `rightTranslation_mem_kFiniteFunctions_realStandardModule` and
   `rightDerivative_mem_kFiniteFunctions_realStandardModule`. The two equations come from
   `mk_rightTranslation_eq` with `blockFrobMap_rightTranslation`, and from
   `mk_rightDerivative_eq` with `blockFrobMap_rightDerivative`.
6. **Left inverse.** `blockFrobMap_blockFrobMap_eq h0 hB` shows that
   `blockFrobMap hB (blockFrobMap h0 g) = g` whenever every Fourier index `j` with
   `(μ j)⁻¹ · μ j ≠ 1` has vanishing coefficients. No such `j` exists, because `μ j ≠ 0`
   (`inv_mul_cancel₀`). So `blockFrobMap h0` has a left inverse and is injective.
7. `mid_pair` rewrites `pre ++ [d, c] ++ post` as `pre ++ d :: c :: post`, and the
   witness is `⟨blockFrobMap h0, injectivity, intertwiner property⟩`.

### From unlinked data to the two conditions

1. **Unlinkedness.** `AreRealBlocksUnlinked (character a) (character b)` compares the
   singleton Mœglin data lists `[character ε_a s_a]` and `[character ε_b s_b]`. It gives
   `¬ IsLinked (character ε_a s_a) (character ε_b s_b)`: there is no `k : ℤ` with `k ≠ 0`,
   `s_a - s_b = k` and `k + ε_a + ε_b` odd.
2. **Excluded values** (`ne_of_not_isLinked`). Let `e ≥ 0` be an integer with
   `e + ε_a + ε_b` even. If `s_a - s_b = e + 2m + 1`, then `k = e + 2m + 1` is a nonzero
   integer with `k + ε_a + ε_b` odd, so the data are linked. If `s_a - s_b = -(e + 2m + 1)`,
   the same holds for `k = -(e + 2m + 1)`. Both cases are excluded.
3. **The parity** (`even_pairParity_add`). `e = pairParity b a = (ε_b + ε_a) mod 2` is a
   nonnegative integer with `e + ε_a + ε_b` even. The witness of evenness is
   `(ε_b + ε_a)/2 + (ε_b + ε_a) mod 2`, and `omega` checks the identity.
4. **Rank.** `pre ++ b :: a :: post` has rank `n`, because it is a permutation of
   `pre ++ a :: b :: post` (`realRank_perm` with `List.Perm.swap`, appended to `pre`).
5. **Conclusion.** Apply `exists_injective_swap` with `c := b` and `d := a`. Then
   `ν = s_a - s_b` and `ε = pairParity b a`, and steps 2 and 3 give `hne` and `hden`. The result
   is `RealInjectiveIntertwinerExists n (pre ++ a :: b :: post) (pre ++ b :: a :: post)`.

## Declarations

- Imported `RealBlockFrobeniusMap.isRealStandardIntertwiner_blockFrobMap`: a Frobenius map with the recurrence for
  `t_p - t_{p+1} + 1` is an `IsRealStandardIntertwiner` into the standard module of its target.
- `exists_injective_swap`: the injective generic swap under `ν ≠ ±(ε + 2m + 1)` described above.
  It has no condition on `Re ν`.
- `ne_of_not_isLinked`: step 2 above, for any `e ≥ 0` with `e + ε₁ + ε₂` even.
- `even_pairParity_add`: step 3 above.
- `realCharacterSwap`: the target statement.

## Sources

- C. Mœglin, *Representations of GL(n) over the real field*, in *Representation theory and
  automorphic forms* (Bailey, Knapp, eds.), Proc. Sympos. Pure Math. 61 (1997)
  (`bailey-knapp-1997-pspm61`), §10, p. 165.
- A. I. Badulescu, D. Renard, *Unitary dual of GL(n) at archimedean places and global
  Jacquet–Langlands correspondence*, Compositio Math. 146 (2010)
  (`badulescu-renard-2010-unitary-dual`), §9.2 and (9.1).
