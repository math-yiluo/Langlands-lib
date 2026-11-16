# Proof of the linked Jacquet functional statement for lists of real characters

Lean module: `Langlands.Representation.Archimedean.RealCharacterCrossing`.
Main theorem:
`Langlands.Archimedean.realCharacterLinkedJacquetFunctional : RealCharacterLinkedJacquetFunctionalStatement`.
The helper definitions and lemmas are in the namespace
`Langlands.Archimedean.RealCharacterCrossing`.

## The statement proved

`RealCharacterLinkedJacquetFunctionalStatement` (module `RealLinkedJacquetFunctionalCases`)
concerns a list `ds` of real blocks with these properties:

- total rank `n`;
- every block is a real character (`IsCharacterList ds`);
- Langlands order (`IsRealLanglandsOrdered ds`);
- two of its Mœglin data are linked (`¬ IsRealMoeglinUnlinked ds`).

The statement asserts that there are:

- a nonzero linear functional `ℓ` on the `O(n)`-finite functions `V(ds)` of the standard module
  of `ds`, which is a real Jacquet functional (`IsRealJacquetFunctional`) with exponents `a` and
  signs `e`;
- a position `p` with `p + 1 < n` and `k : ℕ`;

such that `a_p - a_{p+1} = 1 - k` and `ℓ(π(E_{p+1,p})^k v) = 0` for every `v ∈ V(ds)`. Here
`E_{p+1,p}` is `lowerRootMatrix n p hp`, and `π = realStandardLie n ds` is the action by right
derivatives.

## Role and provenance

The route of this proof is internal. It does not rely on results from the literature. The
statement's own sources are given in the Markdown of `RealLinkedJacquetFunctionalCases` and
`RealLinkedJacquetFunctional`. The linking relation used below is Mœglin's condition (i) for two
characters (`MoeglinDatum.IsLinked`, module `RealLargeStandardIrreducibleReduction`).

The proof works with explicit rank-one operators. Each one exchanges two adjacent characters.
It acts on the `SO(2)`-Fourier modes of the rotation block of those two positions by a scalar
multiplier. This is the familiar `K`-type computation for principal series of `GL_2(ℝ)`, carried
out here directly with the Library modules `RealBlockMultiplier`, `RealBlockFourierFinite` and
`RealBlockJacquetFunctional`.

## Notation

- `PL τ e`, for `τ : Fin n → ℂ` and `e : Fin n → Fin 2`, is the list of the real characters
  `sgn^{e_i} |·|^{τ_i}`, `i < n` (`charData (e i) (τ i)`, Library `RealJacquetFrobeniusProof`).
- `KF n ds` (an `abbrev`) is `V(ds)`. `ρ = realStandardRep n ds` and `π = realStandardLie n ds`.
- `Concl n ds` is the conclusion of the statement for `ds`: the existence of `ℓ, a, e, p, k, hp`
  as above.
- For `r + 1 < n`, `ia hr = r` and `ib hr = r + 1` (Library `RealBlockRotation`). `sw hr` is
  their transposition, `r_r(θ) = blockRotation n r θ` is the rotation in these coordinates, and
  `Φ_j f (g) = blockFourierCoefficient n r j f g = ∫₀^{2π} f(r_r(θ) g) e^{-ijθ} dθ`.
- `ℓ_μ = blockJacquet n ds r μ` is `f ↦ (2π)⁻¹ Σᶠ_j μ_j Φ_j f (1)` for a multiplier `μ : ℤ → ℂ`
  (Library `RealBlockJacquetFunctional`).
- `B f = frobFun ρ ℓ a e f` is the Frobenius function of a Jacquet functional `ℓ`
  (Library `RealJacquetFrobeniusProof`). For a decomposition `g = b κ`, with `b` invertible
  upper triangular and `κ ∈ O(n)`, it is `B f (g) = χ(b) ℓ(ρ(κ) f)`, where
  `χ = diagChar a e` is `b ↦ ∏_i sgn(b_ii)^{e_i} |b_ii|^{a_i}` (Library `frobFun_eq`).
- `e(s) = 1 + s E_{r+1,r}` is `lowerRootElement n r hr s`.

## Proof

### 1. Transport along surjective intertwiners (`concl_of_surjective`)

Let `B : V(ds) → V(ds')` be linear, surjective and compatible with `ρ` and `π`. Then
`Concl n ds'` implies `Concl n ds`. If `ℓ'` is a witness for `ds'`, take `ℓ = ℓ' ∘ B`.

- `ℓ ≠ 0` because `B` is surjective.
- The Jacquet conditions and `ℓ ∘ π(E)^k = 0` pass through `B`, since `B` commutes with `π`
  and hence with `π(E)^k` (induction on `k`).

### 2. The Frobenius map (`frobMap`)

Let `ℓ` be a real Jacquet functional on `V(ds)` with exponents `a` and signs `e`. Then
`frob_mem` shows that `B v` lies in `V(PL (expo a) e)`, where `expo a i = a_i - (n - 1)/2 + i`.
It combines three facts:

- smoothness and the left covariance of `B v` (`contMDiff_frobFun`, `frobFun_left`);
- `O(n)`-finiteness (`frobFun_mem_kFiniteVectors`);
- the induced-block condition, which is vacuous for a list of characters.

`frobMap` is the codomain restriction of the Library `frobLin`. `frobMap_rep` and `frobMap_lie`
say that it intertwines `ρ` and `π`, by `frobLin_codRestrict_rep` and
`frobLin_codRestrict_lie` of `RealLinkedJacquetFunctional`. Finally,
`frobMap_apply_one : (frobMap v)(1) = ℓ v`.

### 3. Crossings (`isJacquet_cross`)

Fix `r + 1 < n`. Let `ε = par hr e = (e_r + e_{r+1}) mod 2`. Let `μ` satisfy
`IsRecurrent (τ_r - τ_{r+1} + 1) ε μ` and `IsSymmetric ε ((-1)^ε) μ`
(Library `RealBlockMultiplier`). Then `ℓ_μ` is a real Jacquet functional on `V(PL τ e)` with:

- exponents `crossExp hr τ`, that is `a_i = τ_{sw(i)} + (n - 1)/2 - i`;
- signs `e ∘ sw`.

This is the Library `isRealJacquetFunctional_blockJacquet`. Two side conditions are checked here:

- The position characters of `PL τ e` are `sgn^{e_i} |·|^{τ_i}` (`PL_position`). They take the
  value `e^{τ_i x}` at `e^x` (`PL_position_exp`) and `(-1)^{e_i}` at `-1`.
- The block exponents become `α_{r+1} + 1` and `α_r - 1`, where `α_i = τ_i + (n - 1)/2 - i`.
  These are `τ_{r+1} + (n - 1)/2 - r` and `τ_r + (n - 1)/2 - (r + 1)`, that is `crossExp`.

Hence `expo (crossExp hr τ) = τ ∘ sw` (`expo_crossExp`). The Frobenius map of a crossing goes
from `V(PL τ e)` to `V(PL (τ ∘ sw) (e ∘ sw))`, the list with the characters at `r, r + 1`
exchanged. Also
`crossExp_sub : a_r - a_{r+1} = τ_{r+1} - τ_r + 1`.

### 4. Generic crossings (`concl_of_generic`)

Let `ν = τ_r - τ_{r+1}`. Assume `0 ≤ re ν` and `ν ≠ ε + 2m + 1` for every `m : ℕ`. Then
`Concl n (PL (τ ∘ sw) (e ∘ sw))` implies `Concl n (PL τ e)`.

- **The multiplier.** Take the Library `genericMultiplier ν ε`. The Library proves its
  recurrence and nonvanishing under `0 < re ν`. Here `isRecurrent_generic` and `generic_ne_zero`
  reprove them under `0 ≤ re ν`: the denominators `ε + 2i + 1 + ν` have real part `≥ 1`
  (`generic_denom_ne_zero`). Its symmetry is the Library `isSymmetric_genericMultiplier`.
  The assumption `ν ≠ ε + 2m + 1` makes every numerator nonzero, so `μ` has no zeros.
- **The inverse crossing.** Let `τ' = τ ∘ sw` and `e' = e ∘ sw`, so `par hr e' = par hr e`.
  The recurrence parameter for `τ'` is `τ'_r - τ'_{r+1} + 1 = 2 - (ν + 1)`. The multiplier
  `k ↦ (μ k)⁻¹` solves it and is symmetric (Library `IsRecurrent.inv`, `IsSymmetric.inv`).
  This gives the crossing `B'` from `V(PL τ' e')` back to `V(PL τ e)` (`PL_sw_sw`).
- **Surjectivity of `B = frobMap`.** For `g ∈ V(PL τ' e')`, compare `B(B' g)` and `g` on `O(n)`.
  Both are sums of their block Fourier modes (`eq_finsum_blockFourierCoefficient`). By the
  Library `blockFourierCoefficient_frobFun`, applied twice,
  `Φ_j(B(B' g))(κ) = μ_j μ_j⁻¹ Φ_j g (κ) = Φ_j g (κ)`. The two functions agree on `O(n)`. Both
  lie in the same principal series, so they are equal
  (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`).
- Section 1 applies to `B`.

### 5. Analytic and algebraic lemmas

- **Polynomials** (`iteratedDeriv_eval`, `iteratedDeriv_eval_eq_zero`): the `m`-th derivative of
  `t ↦ q(t)` is `t ↦ (q^{(m)})(t)`. It vanishes when `deg q < m`.
- **The angle `θ = arctan t`.** Let `S = √(1 + t²)`. Then `1 + it = S e^{iθ}` and
  `1 - it = S e^{-iθ}` (`I_mul_add_one`, `neg_I_mul_add_one`). Hence
  `(1 + it)^a (1 - it)^b = S^{a + b} e^{i(a - b)θ}` (`pow_mul_pow_eq`).
- **Fourier coefficients of `cos^m`** (`coeff_cos_pow_ne_zero`): for `m ≤ 2`, the coefficient of
  `cos^m` at the mode `m mod 2` is nonzero. Write `cos θ = (e^{iθ} + e^{-iθ})/2` and
  `cos² θ = 1/2 + (e^{2iθ} + e^{-2iθ})/4`; the coefficients are `2π`, `π` and `π`.
- **Iwasawa factor of `e(s)`.** Set `b(s) = e(s) r_r(-arctan s)` (`iwaB`). Then
  `e(s) = b(s) r_r(arctan s)` (`iwaB_mul`), and `b(s)` is upper triangular (`iwaB_upper`). Its
  diagonal is `1/S` at `r`, `S` at `r + 1` and `1` elsewhere, with `S = √(1 + s²)`
  (`iwaB_ia`, `iwaB_ib`, `iwaB_of_ne`). These are entrywise computations with
  `cos(arctan s) = 1/S` and `sin(arctan s) = s/S`. Hence `diagChar a e (b(s)) = S^{a_{r+1} - a_r}`
  (`diagChar_iwaB`).
- **Derivatives along `e(s)`** (`hasDerivAt_lowerRoot`, `iteratedDeriv_lowerRoot`): the same
  lemmas as in the proof of `RealTaylorLeftPolynomialStatement`. For smooth `F`, the `m`-th
  derivative of `s ↦ F(e(s))` is `s ↦ (R(E)^m F)(e(s))`, where `R(E)` is the right derivative
  along `E = E_{r+1,r}`.

### 6. A test vector and nonvanishing

- `exists_testVector`: there is `f ∈ V(PL τ e)` with `f(r_r(θ)) = cos^{e_r + e_{r+1}} θ`.
  Start with the sign monomial `κ ↦ ∏_l κ_ll^{e_l}` on `O(n)` (Library `JacquetNonvanishing`).
  It transforms correctly under the sign diagonal matrices, because the position characters
  take the values `(-1)^{e_l}` at `-1` (`PL_position_neg_one_pE`). Extend it to the principal
  series by the Library `principalSeriesExtension`. The extension is `O(n)`-finite, and it lies
  in the standard module because a list of characters has no induced blocks (`mem_KF_of_mem`).
  On `r_r(θ)` the only diagonal entries different from `1` are `cos θ`, at `r` and `r + 1`.
- `exists_blockFourierCoefficient_par_ne_zero`: by `blockFourierCoefficient_eq_coeff`, the
  coefficient `Φ_ε f (1)` of this `f` is the coefficient of `cos^{e_r + e_{r+1}}` at
  `ε = (e_r + e_{r+1}) mod 2`. It is nonzero by section 5.
- `blockJacquet_ne_zero`: assume `μ_j ≠ 0` and `Φ_j v (1) ≠ 0`. If `ℓ_μ = 0`, then the Frobenius
  function of `v` is `0`, and so are its block Fourier coefficients. By
  `blockFourierCoefficient_frobFun` these coefficients are `μ_j Φ_j v (1)`, a contradiction.
  `blockJacquet_PL_ne_zero` applies this with `j = ε` and the test vector: `ℓ_μ ≠ 0` whenever
  `μ_ε ≠ 0`.

### 7. The `k`-th power of `E_{r+1,r}` (`blockJacquet_pow_eq_zero`)

Assume:

- `ℓ_μ` is a real Jacquet functional with exponents `a`, signs `e` and
  `a_r - a_{r+1} = 1 - k`, `k ≥ 1`;
- every mode `j` with `μ_j Φ_j f (1) ≠ 0` for some `f` satisfies `|j| < k` and `j ≡ k - 1 (mod 2)`.

Then `ℓ_μ(π(E_{r+1,r})^k v) = 0` for every `v`. Let `B v` be the Frobenius function.

- `ℓ_μ(π(E)^k v) = (R(E)^k B v)(1)`, by `frobFun_apply_one` and `iterate_rightDerivative_frobFun`
  (module `RealLinkedJacquetFunctional`). By section 5 this is the `k`-th derivative at `0` of
  `s ↦ B v (e(s))`.
- By `frobFun_eq` (Library) and the Iwasawa factor,
  `B v (e(s)) = S^{a_{r+1} - a_r} B v (r_r(θ))` with `θ = arctan s` and `S^{a_{r+1} - a_r} = S^{k-1}`
  (`frobFun_lowerRoot`). By `frobFun_apply_of_mem` and the left rotation rule,
  `B v (r_r(θ)) = (2π)⁻¹ Σᶠ_j μ_j e^{ijθ} Φ_j v (1)` (`frobFun_rotation`).
- By the hypothesis on the modes, the sum runs over `j = k - 1 - 2b`, `b < k`
  (`finsum_eq_sum_jIdx`). By section 5,
  `S^{k-1} e^{i(k-1-2b)θ} = (1 + is)^{k-1-b} (1 - is)^b`.
- So `s ↦ B v (e(s))` is a polynomial of degree `≤ k - 1` in `s`, and its `k`-th derivative
  vanishes.

### 8. The linked adjacent pair (`concl_of_linked_adjacent`)

Let `τ_r - τ_{r+1} = k` with `k > 0` and `k + e_r + e_{r+1}` odd. Then `Concl n (PL τ e)` holds.
The parity condition gives `k - 1 - ε` even.

- Take `μ = binomialMultiplier k ε` (Library). It satisfies `IsRecurrent (k + 1) ε μ` and the
  symmetry, and on the parity class `μ_j ≠ 0 ↔ |j| < k`.
- Section 3 gives the Jacquet functional `ℓ_μ` with exponents `crossExp` and
  `a_r - a_{r+1} = τ_{r+1} - τ_r + 1 = 1 - k`.
- Section 7 applies. By `blockFourierCoefficient_eq_zero_of_not_even`, `Φ_j f = 0` unless
  `j ≡ ε ≡ k - 1`, and `μ_j ≠ 0` forces `|j| < k`.
- Section 6 gives `ℓ_μ ≠ 0`, since `|ε| < k`.
- The conclusion holds with `p = r`.

### 9. Assembly

- `Lk τ e i j`: there is a nonzero integer `m` with `τ_i - τ_j = m` and `m + e_i + e_j` odd. This
  is the definition of `MoeglinDatum.IsLinked` for the data `(1, τ_i, sgn^{e_i})` and
  `(1, τ_j, sgn^{e_j})`.
- `concl_of_lk_adjacent`: assume `Lk` for `(r, r + 1)` and `re τ_{r+1} ≤ re τ_r`. Then
  `m = re(τ_r - τ_{r+1}) ≥ 0`, so `m > 0`, and section 8 applies.
- `concl_of_lk`, by induction on `d`. Hypotheses: `j = i + d + 1`, `Lk τ e i j`,
  `re τ_j ≤ re τ_i`, and `re τ_j ≤ re τ_m` for all `i < m < j`. Conclusion:
  `Concl n (PL τ e)`.
  - For `d = 0` the pair is adjacent.
  - For `d + 1`, let `r = j - 1 > i`, so `re τ_j ≤ re τ_r`.
  - If `Lk τ e r j`, the adjacent case applies.
  - Otherwise `τ_r - τ_j ≠ ε + 2m + 1` for every `m`: such an equality would make `(r, j)`
    linked, since `ε + e_r + e_j` is even. Section 4 reduces the goal to `τ ∘ sw, e ∘ sw`. In
    that list the pair `(i, r)` carries the old characters at `i` and `j`, so all hypotheses
    hold with `d`.
- `concl_of_char`: assume `PL τ e` is in Langlands order and is not Mœglin-unlinked.
  - Langlands order says `re τ_j ≤ re τ_i` for `i < j` (`List.pairwise_map`,
    `List.pairwise_ofFn`).
  - The Mœglin data of `PL τ e` are the character data `(e_i, τ_i)` in order
    (`realMoeglinData_map_character`, `List.map_ofFn`). So some `i < j` satisfies `Lk τ e i j`.
  - Then `concl_of_lk` applies with `d = j - i - 1`.
- **Main theorem.** Let `ds` be a list of characters. Then `ds = cs.map RealBlock.character`
  (`exists_eq_map_character`) and `realRank ds = cs.length` (the existing `Langlands.Archimedean.realRank_map_character`), so
  `n = cs.length`. Also `charData c.parity c.exponent = c` (`charData_eta`): the character
  homomorphism is determined by `character_eq`. With `List.ofFn_getElem` this gives
  `ds = PL τ e` for `τ_i = cs[i].exponent` and `e_i = cs[i].parity`. `concl_of_char` concludes.
