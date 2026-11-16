# The filtration of `[c, d]` on `GL_3(ℝ)` by an isomorphism with `[d, c]`

Lean module: `Langlands.Representation.Archimedean.RealCharacterInducedSwap`, namespace
`Langlands.Archimedean.RealCharacterInducedSwap`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement` (Task 7133). That statement
asks for the adjacent filtration `RealAdjacentFiltration 3 [] [] (character c) (induced d)`
of the `O(3)`-finite functions of the standard module of `[c, d]`, where `c` is a real
character and `d` a complex character of nonzero weight. The module
`RealCharacterInducedPushforward` handles the cases where `b - s` is not a negative integer
greater than `-ℓ`. This module handles the remaining case `b - s = -m₀`, `0 < m₀ < ℓ`, in which
the pushforward route fails. It shows that the `O(3)`-finite functions of `[c, d]` and
`[d, c]` are isomorphic by an exact intertwiner.

The two theorems take as hypotheses statements that are not proved here:

- one of the two landing statements of the module `RealSwapLandingStatement`
  (`RealSwapLandingInducedFirstStatement` or `RealSwapLandingCharacterFirstStatement`);
- `RealOrthogonalBlockUncertaintyStatement` (module
  `RealOrthogonalUncertaintyStatement`).

Surjectivity uses the `K`-type count of the module `RealKTypeTransport` (Worker 764).

The intertwining operators are the block Frobenius maps of Task 7067 (modules
`RealBlockFrobeniusMap`, `RealBlockPositionData`, `RealCharacterPairReducible`). They act on
block Fourier coefficients along one rotation, `Φ^p_j (q f) = μ(j) Φ^p_j f`. The multipliers
are those of the Library module `RealBlockMultiplier`. The route is specific to this project.
No literature statement is formalized, so the module has no sources.

## Notation

- `K(ds)` is `KF 3 ds`, the `O(3)`-finite functions of the standard module of the block list
  `ds` on `GL_3(ℝ)` (module `RealStandardFiltration`). An "exact intertwiner" is an
  intertwiner modulo `⊥` (`IsRealIntertwinerModulo … ⊥`).
- `c = sgn^ε |·|^s` (`c.parity = ε`, `c.exponent = s`). `d` has weight `m ≠ 0` and exponent `t`.
  `ℓ = |m|` (`d.weight.natAbs`), `a = t + ℓ/2`, `b = t - ℓ/2`.
- `χ_A = sgn^{(ℓ+1) mod 2} |·|^a` (`chA`) and `χ_B = |·|^b` (`chB`) are the two position
  characters of the induction block `d`. The position signs of `d` are `((ℓ+1) mod 2, 0)`.
- `r₀`, `r₁`: the rotations in the coordinates `0, 1` and `1, 2`. `Φ^p_j` is the left block
  Fourier coefficient of weight `j` along `r_p` (`blockFourierCoefficient 3 p j`).
- `pairParity c c' = (ε_c + ε_{c'}) mod 2` and `sigma0 c c' = (-1)^{pairParity c c'}`
  (Task 7067).
- In the Lean statements the integer `m₀` is called `m`.

## Declarations

### General lemmas

For data `h : IsBlockFrobData n ds es p ε σ μ` (Task 7067), `blockFrobMap h : K(ds) → K(es)`.

- `frob_injective_of_ne_zero`: if `μ k ≠ 0` for every `k` of the class `k ≡ ε (mod 2)`, then
  `blockFrobMap h` is injective. Off the class the coefficients vanish by parity
  (`blockFourierCoefficient_eq_zero_of_not_even`). The function is then zero by
  `eq_of_blockFourierCoefficient_eq`.
- `modes_of_tail_eq_zero`: let `ℓ > 0`, `ε ∈ {0, 1}`, `ℓ - 1 - ε` even and `σ² = 1`. If the
  map with multiplier `tailMultiplier ℓ ε σ` sends `g` to `0`, then
  `Φ^p_j g = 0` on `O(n)` for all `|j| ≥ ℓ`. On the class, the multiplier is nonzero for
  `|j| > ℓ` (`tailMultiplier_ne_zero_iff`), and `|j| = ℓ` does not occur
  (`abs_lt_of_parity`).
- `eq_zero_of_unitaryCompact`: an element of `K(ds)` that vanishes on `O(n)` is zero
  (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`).
- `modulo_bot_of_coe`: a linear map `K(ds) → K(fs)` with the same underlying functions as an
  exact intertwiner `K(ds) → K(es)` is an exact intertwiner.
- `modulo_symm`: the inverse of a bijective exact intertwiner is an exact intertwiner
  (`modulo_of_comp_surjective`).

### The lists

- `chA`, `chB` with `chA_exponent`, `chB_exponent`.
- `lCD = [c, d]`, `lDC = [d, c]`, `lM = [χ_A, c, χ_B]`, `lP = [c, χ_A, χ_B]`,
  `lQ = [χ_A, χ_B, c]`.
- `posExp_…`: the position exponents of these lists at the positions used below
  (definitional).
- `posChar_lP`, `posChar_lQ`: `P` has the position characters of `[c, d]` and `Q` those of
  `[d, c]`.
- `mem_lCD`: an element of `K(P)` with `Φ¹_k = 0` on `O(3)` for `|k| < ℓ` lies in `K([c, d])`.
  `mem_lDC`: an element of `K(Q)` with `Φ⁰_k = 0` on `O(3)` for `|k| < ℓ` lies in `K([d, c])`.
  Both use `mem_realStandardModule_of_unitaryCompact`, the same position characters, and the
  fact that the only induction block is `d`, at position `1` resp. `0`.
- `filtration_of_surjective`: a surjective exact intertwiner `K([d, c]) → K([c, d])` gives
  `RealAdjacentFiltration 3 [] [] (character c) (induced d)` with the single piece `[d, c]`
  (`HasFiltration.self`, `HasFiltration.map`, `piece_W` of `RealCharacterInducedPushforward`).

### The Frobenius data

- `dataA1`: `A₁ : K([d, c]) → K(M)` along `r₁`, on the class `ε` with sign `(-1)^ε`. This block
  straddles the induction block, so the data is built field by field: position `0` of both
  lists is `(sign (ℓ+1) mod 2, exponent a)`, and the block `1, 2` goes from `(χ_B, c)` to
  `(c, χ_B)`.
- `dataA0`: `A₀ : K(M) → K(P)`, the swap of `χ_A` and `c` along `r₀` (Task 7067's `data_swap`).
- `dataB0`: `B₀ : K([c, d]) → K(M)` along `r₀`, on the class `pairParity c χ_A` with sign
  `sigma0 c χ_A`. It straddles the induction block and is built field by field: the block
  `0, 1` goes from `(c, χ_A)` to `(χ_A, c)`, and position `2` of both lists is `χ_B`.
- `dataB1`: `B₁ : K(M) → K(Q)`, the swap of `c` and `χ_B` along `r₁` (`data_swap`).

### The two cases

- `parity_cases`: `ε ∈ {0, 1}`.
- `pairParity_c_chA`, `pairParity_chB_c` (with their `natAbs` versions): the explicit classes.
  `even_class_c_chA`, `sign_class_c_chA`: the class and sign of `c, χ_A` are those of
  `ℓ + 1 + ε`. `even_class_chB_c`, `sign_class_chB_c`: those of `χ_B, c` are those of `ε`.
- `filtration_tail_first`: assume `RealSwapLandingInducedFirstStatement` and the uncertainty
  statement. Let `0 < m₀ < ℓ`, `b - s = -m₀` (stated as `(chB d).exponent - c.exponent = -m₀`),
  and `m₀ + ε` odd. Then `RealAdjacentFiltration 3 [] [] (character c) (induced d)` holds, with
  the single piece `[d, c]`.

  Proof. `A₁` has multiplier `tailMultiplier m₀ ε (-1)^ε`, which solves the recurrence for
  `δ = b - s + 1 = 1 - m₀` (`isRecurrent_tailMultiplier`; `m₀ - 1 - ε` is even). So `A₁` is
  an exact intertwiner (`isRealIntertwinerModulo_blockFrobMap`). `A₀` has multiplier
  `genericMultiplier (ℓ - m₀) (pairParity c χ_A)` with `ν₀ = a - s = ℓ - m₀ > 0`. It is an exact
  intertwiner, and it is injective because its multiplier has no zeros: a zero needs
  `ℓ - m₀ = pairParity c χ_A + 2i + 1`, which has the wrong parity. The landing statement
  applies to `f`, `A₁ f`, `A₀ (A₁ f)` with `δ = 1 - m₀` (note `δ + ℓ = ν₀ + 1`; the classes are
  moved by `isRecurrent_of_even`, `isSymmetric_of_even`). So `A₀ ∘ A₁` lands in `K([c, d])` by
  `mem_lCD`; call the restricted map `T`. It is an exact intertwiner (`modulo_comp_bot`,
  `modulo_bot_of_coe`).

  `T` is injective. If `T f = 0`, then `A₁ f = 0` because `A₀` is injective. So `f` has no
  modes `|j| ≥ m₀` along `r₁` (`modes_of_tail_eq_zero`). As a function of `K([d, c])` it has no
  modes `|j| < ℓ` along `r₀`. By the uncertainty statement (`p = 0`, `q = 1`, `n = ℓ`,
  `n' = m₀ < ℓ`), `f` vanishes on `O(3)`, so `f = 0`. `T` is onto by
  `RealKTypeTransport.surjective_of_injective_induced_character`. Conclude with
  `filtration_of_surjective`.
- `filtration_tail_second`: assume `RealSwapLandingCharacterFirstStatement` and the uncertainty
  statement. Let `0 < m₀ < ℓ`, `b - s = -m₀` and `m₀ + ε` even. Then the same filtration exists,
  with the single piece `[d, c]`.

  Proof. `B₀` has multiplier `tailMultiplier (ℓ - m₀) (pairParity c χ_A) (sigma0 c χ_A)`, which
  solves the recurrence for `δ = s - a + 1 = 1 - (ℓ - m₀)` (`ℓ - m₀ - 1 - pairParity c χ_A`
  is even). `B₁` has multiplier `genericMultiplier m₀ (pairParity χ_B c)` with
  `ν₁ = s - b = m₀ > 0`. It is injective because a zero needs `m₀ = pairParity χ_B c + 2i + 1`,
  which has the wrong parity. Both are exact intertwiners. The landing statement applies with
  `δ = 1 - (ℓ - m₀)` (note `δ + ℓ = m₀ + 1`), so `B₁ ∘ B₀` lands in `K([d, c])` by `mem_lDC`.
  Call the restricted map `E`. If `E f = 0`, then `B₀ f = 0`, so `f` has no modes
  `|j| ≥ ℓ - m₀` along `r₀`. As a function of `K([c, d])` it has no modes `|j| < ℓ` along `r₁`.
  The uncertainty statement (`p = 1`, `q = 0`, `n = ℓ`, `n' = ℓ - m₀ < ℓ`) gives `f = 0`. `E` is
  onto by `RealKTypeTransport.surjective_of_injective_character_induced`. So `E` is bijective.
  Its inverse is an exact intertwiner (`modulo_symm`) and is onto. Conclude with
  `filtration_of_surjective`.
