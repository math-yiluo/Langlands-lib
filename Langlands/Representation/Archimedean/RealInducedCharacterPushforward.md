# The induced–character filtration on `GL₃(ℝ)`: the pushforward along the tail maps

Module `Langlands.Representation.Archimedean.RealInducedCharacterPushforward` (namespace
`Langlands.Archimedean.RealInducedCharacter`).

## Role and provenance

This module is an internal step of the proof of `RealInducedCharacterFiltrationStatement`
(Task 7134; see `RealInducedCharacterFiltration.md`). It covers every case except the hard
case `t_c - a = -m'` (module `RealInducedCharacterHard`). In these cases it builds the
filtration of the standard module of `[d, c]` on `GL₃(ℝ)` from the filtration for two
characters, by pushing forward along the tail maps of `RealInducedCharacterMaps`. The
argument assumes the landing statement `RealSwapLandingInducedFirstStatement` (module
`RealSwapLandingStatement`). No literature statement is formalized.

Notation. `d` has weight `m` and exponent `t`, with `ℓ = |m| > 0`. `c` has parity `ε` and
exponent `s`. `a = aExp d = t + ℓ/2` and `b = bExp d = t - ℓ/2`. `c_a = ca d s_a` and
`c_b = cb d s_b`, with `s_a + s_b ≡ ℓ + 1 (mod 2)` (hypothesis `hs`). `Φ^p_j` is the block
Fourier coefficient along `r_p`. `KF 3 ds` denotes the `O(3)`-finite functions of
`realStandardModule 3 ds`.

The maps used are:

* `T₁ : [c, c_b, c_a] → [c, d]`, the tail map at position `1`, and
  `T₀ : [c_b, c_a, c] → [d, c]`, the tail map at position `0` (`data_tail`);
* `Q₂ : [c, c_b, c_a] → [c_b, c, c_a]`, a swap with a multiplier `μ₀` symmetric for
  `pairParity c_b c` (`data_swap` of the Library module `RealCharacterPairReducible`);
* `Q₁ : [c_b, c, c_a] → [c_b, c_a, c]`, a swap with a multiplier `μ₁` symmetric for
  `pairParity c_a c`.

## Signs

* `pow_eq_pow_mul_pow_of_mod`: if `x² = 1` and `p ≡ q + e (mod 2)`, then `x^p = x^q · x^e`.
* `realPositionCharacter_signUnit`: the position character at a sign `sgn x` is
  `sgn(x)^{s_i}`, where `s_i = realPositionSign ds i`.
* `sgnDet_signDiagonal`: the sign of the determinant of `diag(sgn a)` is `∏ sgn(a_i)`.
* `principalSeries_signDiagonal`: a principal series function `G` satisfies
  `G(diag(sgn a) κ) = ∏ sgn(a_i)^{s_i} · G(κ)`. This follows from the left `B`-equivariance
  of the principal series.
* `principalSeries_signDiagonal_twist`: suppose the position signs of `X` agree modulo `2`
  with those of `Y` shifted by `e`. Then a principal series function for `X` transforms under
  sign matrices by the character of `Y` times `sgnDet^e`. This is the form of the hypothesis
  `hGM` of `highModes_eq_zero_mirror`.

## The descent through the tail map

* `cTest c s_a = charData (s_a + ε) s`: the character `c'` of the mirror landing. It has the
  exponent of `c` and parity `s_a + ε`.
* `pairParity_ca`, `sigma0_ca`, `even_pairParity_cb`, `sigma0_cb`: the parity classes and
  symmetry signs of `Q₁` and `Q₂` agree, modulo `2`, with those that
  `highModes_eq_zero_mirror` requires for `c' = cTest c s_a`.
* `highModes_of_tail_eq_zero`: if `T₁ g = 0`, then `Φ¹_j g = 0` on `O(3)` for `|j| ≥ ℓ`. On
  the parity class, `|j| = ℓ` is excluded by parity, and for `|j| > ℓ` the tail multiplier is
  nonzero (`tailMultiplier_ne_zero_iff`). Off the parity class, the coefficients vanish
  anyway.
* `sign_high_twist`: the position signs of `[sgn^{s_b}|·|^a, sgn^{s_a}|·|^b, c]` are those
  of `[d, c']` shifted by `s_a`. The proof checks each of the three positions.
* `descent`: assume `hL`, the symmetries of `μ₀, μ₁`, and the recurrences
  `IsRecurrent (s - b + 1) (pairParity c_b c) μ₀` and
  `IsRecurrent (s - a + 1) (pairParity c_a c) μ₁`. If `T₁ g = 0`, then `T₀ (Q₁ (Q₂ g)) = 0`.
  *Proof.* Put `g₁ = Q₂ g` and `g₂ = Q₁ g₁`. Let `G = H g₂`, where `H` is the projection
  `data_high` onto the block-`0` modes `|j| ≥ ℓ`; `G` lies in the principal series of
  `[sgn^{s_b}|·|^a, sgn^{s_a}|·|^b, c]`. Apply `highModes_eq_zero_mirror` with
  `c' = cTest c s_a`, `δ = s - a + 1`, `e = s_a`, and the functions `f = g`, `g₁`, `g₂`,
  `G`. Its hypotheses hold as follows:
  - the high block-`1` modes of `g` vanish by `highModes_of_tail_eq_zero`;
  - the multiplier relations hold by `blockFourierCoefficient_blockFrobMap`;
  - `μ₀` solves the recurrence for `δ + ℓ = s - b + 1`, since `a - b = ℓ`;
  - the sign law of `G` follows from `principalSeries_signDiagonal_twist` and
    `sign_high_twist`.
  The theorem gives `Φ⁰_j g₂ = 0` for `|j| ≥ ℓ`, and `tail_eq_zero` gives `T₀ g₂ = 0`.
* `exists_lift`: under the same hypotheses, there is an exact intertwiner
  `L : KF 3 [c, d] → KF 3 [d, c]` with `L ∘ T₁ = T₀ ∘ Q₁ ∘ Q₂`. Take
  `L = (T₀ ∘ Q₁ ∘ Q₂) ∘ T₁'`, where `T₁'` is the inverse tail map (`data_tailInv`). Since
  `T₁ ∘ T₁' = id`, the function `T₁' (T₁ g) - g` is killed by `T₁`, and `descent` gives the
  factorization. `L` is an exact intertwiner by `modulo_of_comp_surjective` (module
  `RealStandardFiltration`), because `T₀ ∘ Q₁ ∘ Q₂` is one (`modulo_comp_bot`) and `T₁` is a
  surjective exact intertwiner.

## The swaps and the reducible pieces

* `swap_surjective`: a swap whose multiplier has no zeros is surjective. Its preimage is given
  by the unswap map `data_unswap` and `blockFrobMap_blockFrobMap_eq`.
* `reducible_pieces`: assume `t_d - t_c = ℓ' > 0` is an integer with
  `ℓ' - 1 ≡ pairParity c d (mod 2)`. Then the map `q₁` from
  `pre ++ indBlock c d ℓ' ++ post` (`data_q1`) is an intertwiner modulo the range of the
  binomial swap `q₀` (`data_q0`), and every `g` is `q₀ a + q₁ b`. The proof repeats the
  argument of `realAdjacentFiltration_of_reducible` (Library) while keeping the
  maps:
  - `q₁` has the left inverse `D` (`data_D`, tail multiplier), by
    `blockFrobMap_blockFrobMap_eq` and the block Fourier condition of `pairInduced c d ℓ'`;
  - `ker D ⊆ range q₀` (`ker_le_range`, with `data_B`);
  - `isRealIntertwinerModulo_of_leftInverse` gives the intertwining modulo `range q₀`;
  - finally `g = q₀ a + q₁ (D g)`.

## The pushforward

* `tail_swap_surjective`: if `μ₁` has no zeros, every `f ∈ KF 3 [d, c]` is `T₀ (Q₁ h)`. This
  combines `tail_surjective` and `swap_surjective`.
* `re_bExp_lt`: if `Re t_d < Re s`, then `0 < Re (s - b)`.
* `pushforward_generic`: assume that `Q₁` has the generic multiplier for `ν₁ = s - a` with
  nonvanishing denominators and without zeros (`hden₁`, `hne₁`). Assume that `Q₂` has the
  generic multiplier for `ν₂ = s - b` with `0 < Re ν₂` and without zeros (`hne₂`). Then
  `RealAdjacentFiltration 3 [] [] (induced d) (character c)` holds, with the single piece
  `[c, d]` and the map `L` of `exists_lift`. `L` is surjective: by `tail_swap_surjective` and
  `swap_surjective`, every `f` is `T₀ (Q₁ (Q₂ g)) = L (T₁ g)`. The recurrences come from
  `isRecurrent_genericMultiplier` and `isRecurrent_genericMultiplier'`.
* `pushforward_reducible`: assume `Q₁` is as above and `ν₂ = s - b = ℓ'` is an integer with
  `ℓ' > ℓ` and `ℓ' - 1 ≡ pairParity c_b c (mod 2)`. Take `Q₂ = q₀` with the binomial
  multiplier (`isRecurrent_binomialMultiplier`). Then the filtration holds with two pieces:
  `[c, d]` with the map `L`, and `[induced (pairInduced c_b c ℓ'), c_a]` with the map
  `P = T₀ ∘ Q₁ ∘ q₁`. `P` is an intertwiner modulo `range L`, since
  `T₀ ∘ Q₁ ∘ q₀ = L ∘ T₁` maps into `range L`. The second piece is admissible in
  `RealAdjacentFiltration`:
  - its exponent support `[s, b, a]` (`realExponentSupport_pairInduced_eq`) is a
    permutation of the support `[a, b, s]` of `[d, c]`;
  - its weight square sum `ℓ'²` exceeds `ℓ²`.
  Every `f = T₀ (Q₁ h)` with `h = q₀ a + q₁ b` lies in `range L + range P`.
