# The filtration of `[c, d]` on `GL_3(ℝ)` by pushforward from a principal series

Lean module: `Langlands.Representation.Archimedean.RealCharacterInducedPushforward`, namespace
`Langlands.Archimedean.RealCharacterInducedPushforward`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. That statement
asks for the adjacent filtration `RealAdjacentFiltration 3 [] [] (character c) (induced d)`
of the `O(3)`-finite functions of the standard module of `[c, d]`, where `c` is a real
character and `d` a complex character of nonzero weight. This module proves it in two of the
cases, `filtration_generic` and `filtration_reducible` (described below). Both take the landing
statement `RealSwapLandingCharacterFirstStatement` (module `RealSwapLandingStatement`)
as a hypothesis `hL`. That statement is not proved here.

The idea is the classical one: realize the induction block `d` inside a principal series
`[χ_b, χ_a]` of `GL_2(ℝ)`, build the filtration on the principal series of `GL_3(ℝ)` by
intertwining operators between the orderings of three characters, and push it forward. Here
the intertwining operators are the block Frobenius maps (modules
`RealBlockFrobeniusMap`, `RealBlockPositionData`, `RealCharacterPairFiltration`,
`RealCharacterPairReducible`): a map on block Fourier coefficients along one rotation,
`Φ^p_j (q f) = μ(j) Φ^p_j f`, with a multiplier `μ`. The multipliers are those of the Library
module `RealBlockMultiplier` (`genericMultiplier`, `binomialMultiplier`, `tailMultiplier`).
The route through these maps and the landing statement is specific to this project. No
literature statement is formalized, so the module has no sources.

## Notation

- `K(ds)` is `KF 3 ds`, the `O(3)`-finite functions of the standard module of the block list
  `ds` on `GL_3(ℝ)` (module `RealStandardFiltration`). `IsRealIntertwinerModulo`,
  `HasFiltration`, `IsAdjacentPiece` and `RealAdjacentFiltration` are as there. An "exact
  intertwiner" is an intertwiner modulo `⊥`.
- `c = sgn^ε |·|^s` (`c.parity = ε`, `c.exponent = s`); `d` has weight `m ≠ 0` and exponent
  `t`; `ℓ = |m|` (`d.weight.natAbs`); `a = t + ℓ/2`, `b = t - ℓ/2`.
- For a sign `s_b ∈ Fin 2`, put `s_a = s_b + ℓ + 1 mod 2`, `χ_b = sgn^{s_b} |·|^b` (`chiB`),
  `χ_a = sgn^{s_a} |·|^a` (`chiA`), and `d' = pairInduced χ_b χ_a ℓ` (`dP`), the induction
  block of weight `ℓ` and exponent `(a + b)/2 = t`.
- The lists: `X = [c, χ_b, χ_a]` (`lX`), `Y = [χ_b, c, χ_a]` (`lY`), `Z = [χ_b, χ_a, c]`
  (`lZ`), `V = [c, d']` (`lV`), `W = [d', c]` (`lW`),
  `G = [c, sgn^{s_b}|·|^a, sgn^{s_a}|·|^b]` (`lG`), and, for `ℓ' ∈ ℕ`,
  `R = [χ_b, induced(pairInduced c χ_a ℓ')]` (`lR`).
- `pairParity c c' = (ε_c + ε_{c'}) mod 2`, and `sigma0 c c' = (-1)^{pairParity c c'}`
  (modules `RealCharacterPairData` and `RealCharacterPairReducible`).
- `w = b - s`, the difference of exponents of the first swap.

## Declarations

### Parity bookkeeping

- `fin2 k = k mod 2` as an element of `Fin 2`, with `fin2_val`.
- `neg_one_pow_congr`, `neg_one_pow_eq_mul`: `(-1)^k` depends on `k mod 2`.
- `isRecurrent_of_even`, `isSymmetric_of_even`: `IsRecurrent δ ε μ` and `IsSymmetric ε σ μ`
  depend only on the parity class of `ε` (and on `σ` up to equality).
- `pairParity_nonneg`: `0 ≤ pairParity c c'`.
- `ne_intCast_of`: if `w = k` for an integer `k` only when `k = 0`, then `w ≠ q` for every
  nonzero integer `q`.

### The generic multiplier without a positivity assumption

The Library proves the recurrence and nonvanishing of `genericMultiplier ν ε` under
`0 < Re ν`. These versions assume only what the proof uses.

- `genericSeq_succ'`: if `ε + 2i + 1 + ν ≠ 0` for all `i ∈ ℕ`, then
  `genericSeq ν ε (m+1) (ν + 1 + ε + 2m) = (ε + 2m + 2 - (ν + 1)) genericSeq ν ε m`.
- `isRecurrent_genericMultiplier'`: under the same assumption and `ε ∈ {0, 1}`,
  `IsRecurrent (ν + 1) ε (genericMultiplier ν ε)` (via the Library's `isRecurrent_extend`).
- `genericMultiplier_ne_zero'`: if moreover `ν ≠ ε + 2m + 1` for all `m ∈ ℕ`, the multiplier has
  no zeros: every factor `(ν - (ε + 2i + 1)) / (ε + 2i + 1 + ν)` of `genericSeq` is nonzero.

### Frobenius maps

For data `h : IsBlockFrobData n ds es p ε σ μ` (module `RealBlockFrobeniusMap`), `blockFrobMap h : K(ds) → K(es)`.

- `frob_inv_of_ne_zero`: if `μ` has no zeros on the class `k ≡ ε`, the map with the inverse
  multiplier `k ↦ (μ k)⁻¹` is a right inverse (`blockFrobMap_blockFrobMap_eq`).
- `tail_inv`: let `ℓ > 0`, `ε ∈ {0, 1}`, `ℓ - 1 - ε` even, `σ² = 1`, `D` the map with
  multiplier `tailMultiplier ℓ ε σ` into a list `es` with an induction block of weight `ℓ` at
  `p`, and `q` the map with the inverse multiplier. Then `D (q f) = f`. Proof: where
  `tailMultiplier ℓ ε σ j = 0` one has `|j| < ℓ` (`tailMultiplier_ne_zero_iff`,
  `abs_lt_of_parity`), and the modes `|j| < ℓ` of a function of the standard module with an
  induction block of weight `ℓ` at `p` vanish.
- `ker_tail_le_range`: with `h₀` the map with multiplier `binomialMultiplier ℓ ε` (and `hB` its
  inverse-multiplier map) and `D` the tail map out of its target, `ker D ≤ range h₀`. Proof:
  `ker_le_range` (module `RealCharacterPairReducible`); a zero of the binomial multiplier has `|j| ≥ ℓ`, and there the
  tail multiplier is nonzero.

### Filtrations with two pieces

- `hasFiltration_two`: let `q₀ : K(e₀) → K(ds)` be an exact intertwiner, and
  `q₁ : K(e₁) → K(ds)` an intertwiner modulo `range q₀`, such that every `g ∈ K(ds)` is
  `q₀ a + q₁ b`. If `P e₀` and `P e₁`, then `HasFiltration n ds P` (index type `Fin 2`).

### Standard modules with the same data

- `abs_weight_eq`: complex character data with the same `natAbs` of weights have the same
  `|weight|`.
- `realStandardModule_congr`: two block lists with the same position characters, and induction
  blocks of the same weights at the same positions, have the same standard module (from
  `mem_realStandardModule_iff`).
- `realInducedBlockAt_induced_character`: the only induction block of `[d, c]` is `d` at
  position `0`.
- `kf_character_induced_congr`, `kf_induced_character_congr`: if `d'` and `d` have the same
  `ℓ` and the same exponent, then `K([c, d']) = K([c, d])` and `K([d', c]) = K([d, c])`.

### The characters `χ_b`, `χ_a` and the block `d'`

- `chiB`, `chiA`, `dP` as in the notation, with `chiB_exponent`, `chiA_exponent`,
  `chiB_parity`, `chiA_parity_val` (`s_a = (s_b + ℓ + 1) mod 2`), `chiA_sub_chiB`
  (`a - b = ℓ`), `even_pairParity_chiB_chiA` (`ℓ - 1 - pairParity χ_b χ_a` is even),
  `dP_weight_natAbs`, `dP_abs_weight`, `dP_exponent` (`d'` has exponent `t`).
- `kf_V : K(V) = K([c, d])` and `kf_W : K(W) = K([d, c])`.

### The lists and the Frobenius data

All data come from the constructors of the modules `RealCharacterPairReducible` and
`RealBlockFrobeniusMap`: `data_D` and `data_q1` (tail maps onto an
induction block and their inverses), `data_swap` and `data_unswap` (swaps of two characters
and their inverses), and `IsBlockFrobData.of_mid`.

- `dataD1`: the tail map `D₁ : K(X) → K(V)` along the block `1, 2`, multiplier
  `tailMultiplier ℓ (pairParity χ_b χ_a) (-1)^{s_a}`; `dataS1` its inverse-multiplier map
  `K(V) → K(X)`.
- `dataT0`: the tail map `T₀ : K(Z) → K(W)` along the block `0, 1`, the same multiplier;
  `dataS0` its inverse-multiplier map `K(W) → K(Z)`.
- `dataQ1`, `dataQ1'`: for a multiplier `μ` with `IsSymmetric (pairParity c χ_b) (sigma0 c χ_b) μ`,
  the swap `Q₁ : K(Y) → K(X)` along `0, 1` and the inverse-multiplier map `K(X) → K(Y)`.
- `dataQ2`, `dataQ2'`: likewise the swap `Q₂ : K(Z) → K(Y)` along `1, 2` (for `c` and `χ_a`)
  and its inverse-multiplier map.
- `highIndicator j = 1` if `|j| ≥ ℓ`, else `0`; it is symmetric with sign `1`
  (`isSymmetric_highIndicator`).
- `dataG`: the projection `K(X) → K(G)` onto the modes `|j| ≥ ℓ` along `1, 2`, with multiplier
  `highIndicator`, built with `of_mid` (the middle lists `[χ_b, χ_a]` and
  `[sgn^{s_b}|·|^a, sgn^{s_a}|·|^b]`).

### Sign equivariance of the projection

- `pow_eq_pow_mul_pow_of_sq`: if `x² = 1` and `k ≡ m + e (mod 2)`, then `x^k = x^m x^e`.
- `posChar_signUnit`: a position character at the sign unit of `x` is
  `sgn(x)^{(position sign)}`.
- `signReal_sq`: `sgn(r)² = 1`. `sgnDet_signDiagonal`: `sgnDet` of the diagonal sign matrix of
  `a` is `∏ sgn(a_i)` (`Matrix.det_diagonal`, `abs_signReal`).
- `cPP = sgn^{ε + s_a} |·|^s` (`cPP_parity_val`).
- `sign_equivariance`: for `G ∈ K(G)`, `a ∈ (ℝˣ)³` and `κ ∈ O(3)`,
  `G(diag(sgn a) κ) = χ(sgn a) · sgnDet(diag(sgn a))^{s_a} · G(κ)`, where `χ` is the principal
  series character of the position characters of `[cPP, d]`. Proof: the left `diag(sgn a)`
  equivariance of the standard module (`PartialJacquet.signDiagonal_toUnits`,
  `JacquetKernel.principalSeriesCharacter_sign`), then a comparison of the position signs at
  each of the three positions: the signs of `G` are `(ε, s_b, s_a)`, those of `[cPP, d]` are
  `(ε + s_a, (ℓ + 1) mod 2, 0)`, and `s_b ≡ ℓ + 1 + s_a`.

### The kernel of `T₀`

- `even_Q1_class`, `sigma0_chiB`: the class and sign of the first swap, `pairParity c χ_b`
  and `sigma0 c χ_b`, are those of the class `ℓ + 1 + (ε + s_a)` used by the landing step.
- `kernel_step`: assume `hL` and `ℓ > 0`. Let `Q₁ : K(Y) → K(X)` and `Q₂ : K(Z) → K(Y)` be swaps
  whose multipliers `μ₀`, `μ₁` satisfy `IsRecurrent (b - s + 1) (pairParity c χ_b) μ₀` and
  `IsRecurrent (a - s + 1) (pairParity c χ_a) μ₁`. If `T₀ z = 0`, then
  `D₁ (Q₁ (Q₂ z)) = 0`.

  Proof. Since `T₀ z = 0`, the coefficients `Φ⁰_j z` vanish where the tail multiplier is
  nonzero, which on the class is `|j| > ℓ` (`tailMultiplier_ne_zero_iff`; `|j| = ℓ` does not
  occur on the class, `abs_lt_of_parity`); off the class they vanish by parity.
  So `z` has no modes `|j| ≥ ℓ` along the first rotation. Put `g = Q₁ (Q₂ z)` and let `G` be its
  projection onto the high modes along the second rotation (`dataG`). By `sign_equivariance`
  and `RealSwapFLanding.highModes_eq_zero` (with `c'' = cPP`, `δ = b - s + 1`, `e = s_a`;
  note `a - s + 1 = δ + ℓ`), `Φ¹_j g = 0` for `|j| ≥ ℓ`. The coefficients of `D₁ g` are
  `tailMultiplier · Φ¹_j g`, which vanish for `|j| ≥ ℓ`; for `|j| < ℓ` they vanish because
  `D₁ g` lies in the standard module of `V`, whose induction block `d'` has weight `ℓ`. So
  `D₁ g = 0` (`eq_of_blockFourierCoefficient_eq`).

### Descent and assembly

- `descend`: let `T : K(es) → K(es')` be an exact intertwiner with a right inverse `S`, and `P`
  an intertwiner modulo `M` out of `K(es)` with `P z = 0` whenever `T z = 0`. Then `P ∘ S` is an
  intertwiner modulo `M` and `P (S (T z)) = P z`. Proof: `z - S (T z)` lies in the kernel of
  `T`; then `modulo_of_comp_surjective`.
- `range_comp_eq`: then `range (P ∘ S) = range P`.
- `generic_swap`: a Frobenius map with multiplier `genericMultiplier ν ε`, where
  `ν = t_p - t_{p+1}` and `ε + 2i + 1 + ν ≠ 0`, `ν ≠ ε + 2m + 1` for all `i, m ∈ ℕ`, is an exact
  intertwiner (`isRealIntertwinerModulo_blockFrobMap` with `isRecurrent_genericMultiplier'`)
  with the inverse-multiplier map as a right inverse (`frob_inv_of_ne_zero`).
- `hasFiltration_of_stage` (one piece): if `P : K(Z) → K(V)` is a surjective exact intertwiner
  vanishing on the kernel of an exact intertwiner `T : K(Z) → K(W)` with a right inverse `S`,
  then `K(V)` has a filtration whose only piece is `W`, by `P ∘ S`
  (`HasFiltration.self` and `HasFiltration.map`).
- `hasFiltration_of_stages` (two pieces): let `A : K(Y) → K(V)` be a surjective exact
  intertwiner, `Q : K(Z) → K(Y)` an exact intertwiner with `A ∘ Q` vanishing on the kernel of
  `T` (as above), and `q : K(R) → K(Y)` an intertwiner modulo `range Q` with a left inverse `D`
  whose kernel lies in `range Q`. Then `K(V)` has a filtration with the pieces `W` (by
  `A ∘ Q ∘ S`, exact) and `R` (by `A ∘ q`, modulo `A(range Q) = range (A ∘ Q ∘ S)`). Every
  `A y` is `(A ∘ Q ∘ S)(T z) + A (q (D y))`, where `y - q (D y) = Q z`.

### The maps `D₁`, `T₀` and the first swap

- `tail_recurrent`: the tail multiplier satisfies the recurrence for `δ = b - a + 1 = 1 - ℓ`
  (`isRecurrent_tailMultiplier`). `posExp_lX_1`, `posExp_lX_2`, `posExp_lZ_0`, `posExp_lZ_1`:
  the position exponents of `X` at `1, 2` and of `Z` at `0, 1` are `b, a`.
- `modulo_D1`, `modulo_T0`: `D₁` and `T₀` are exact intertwiners. `D1_S1`, `T0_S0`: they have
  right inverses (`tail_inv`).
- `mu0 = genericMultiplier (b - s) (pairParity c χ_b)` and
  `mu1 = genericMultiplier (a - s) (pairParity c χ_a)`, symmetric with the swap signs
  (`symm_mu0`, `symm_mu1`, from `isSymmetric_genericMultiplier`).
- `stage1`: if `pairParity c χ_b + 2i + 1 + w ≠ 0` and `w ≠ pairParity c χ_b + 2m + 1` for all
  `i, m ∈ ℕ`, then `D₁ ∘ Q₁ : K(Y) → K(V)` (with `mu0`) is a surjective exact intertwiner.

### The pieces

- `piece_W`: `[d, c]` is an adjacent piece (the swap `[y, x]`).
- `piece_R`: if `a - s = ℓ'` with `ℓ < ℓ'`, then `R = [χ_b, induced(c, χ_a)]` (weight `ℓ'`) is
  an adjacent piece: its exponent support `[b, a, s]` (`realExponentSupport_pairInduced_eq`)
  is the reverse of `[s, a, b]`, and `ℓ² < ℓ'²`.
- `realAdjacentFiltration_of_lV`: a filtration of `K(V)` whose pieces have the same
  `O(3)`-finite functions as adjacent pieces gives `RealAdjacentFiltration 3 [] [] c d`
  (`kf_V`, `HasFiltration.congr`, `HasFiltration.of_eq_pieces`, `realAdjacentFiltration_iff`).

### The two cases

- `filtration_generic` (case (a)): assume `hL`, `ℓ > 0`, that `w = b - s` is an integer only if
  it is `0`, and `ε + s_b` odd. Then `RealAdjacentFiltration 3 [] [] (character c) (induced d)`
  holds, with the single piece `[d, c]`.

  Proof. Both swaps use generic multipliers: `mu0` with `ν = w`, and `mu1` with
  `ν = a - s = w + ℓ`. All their numerators and denominators are nonzero, since each vanishing
  would make `w` a nonzero integer. Three of the four cases give `w` of a definite sign; the
  fourth, `a - s = pairParity c χ_a + 2m + 1`, gives `w = pairParity c χ_a + 2m + 1 - ℓ`,
  which is odd because `ε + s_b` odd makes `pairParity c χ_a ≡ ℓ (mod 2)`. So `D₁ ∘ Q₁` is onto (`stage1`), `Q₂` is onto (`generic_swap`),
  and `D₁ ∘ Q₁ ∘ Q₂` vanishes on `ker T₀` (`kernel_step`). Apply `hasFiltration_of_stage` with
  `T = T₀`, `S = S₀`, and identify `K(W) = K([d, c])`.
- `filtration_reducible` (case (b)): assume `hL`, `ℓ > 0`, `w = k` for a natural number
  `k > 0`, and `ε + s_b ≡ k (mod 2)`. Then the same filtration exists, with the pieces `[d, c]`
  and `R` for `ℓ' = k + ℓ`.

  Proof. The first swap is generic as in case (a): its parity class is `k mod 2`, so its
  denominators `pairParity + 2i + 1 + k` are positive and its numerators vanish only if
  `k = pairParity + 2m + 1`, which has the wrong parity. The second swap has `a - s = ℓ'`, and
  `ℓ' - 1 - pairParity c χ_a` is even; it uses the reducible data of `RealCharacterPairReducible`: `Q₂` with
  `binomialMultiplier ℓ'`, the tail map `D : K(Y) → K(R)` and its inverse-multiplier map
  `q : K(R) → K(Y)`. Here `D (q f) = f` (`tail_inv`), `ker D ≤ range Q₂` (`ker_tail_le_range`),
  and `q` is an intertwiner modulo `range Q₂` (`isRealIntertwinerModulo_of_leftInverse`).
  Apply `hasFiltration_of_stages` with `A = D₁ ∘ Q₁`, `Q = Q₂`, `T = T₀`, and identify the
  pieces with `[d, c]` (`kf_W`) and `R` (`piece_R`, since `ℓ < ℓ'`).
