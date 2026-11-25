# A witness for the nonvanishing of the pairing along a standard parabolic subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviWitness`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It
states and proves `Langlands.Archimedean.RealLeviWitnessStatement` (proof `realLeviWitness`).
The module combines the density step (`RealLeviDensityStatement`) with the nonvanishing step
(`RealLeviNonvanishingStatement`) of the single-shot Langlands-quotient argument. It produces the
nonzero value of the pairing `Θ(u, h₀)` that the limit argument (`RealLeviLimitStatement`) needs.
No literature statement is claimed and nothing is cited; the provenance is internal ("derived").
Unprefixed names below are in the namespace `Langlands.Archimedean.RealLeviWitness`.

## Notation

As in `RealLeviDensity.md` and `RealLeviNonvanishing.md`. For `dss : Fin c → List RealBlock`:
`sz dss i = realRank (dss i)`, `N = ∑_i sz dss i`, `flat dss = dss 0 ++ ⋯ ++ dss (c-1)`,
`cl dss i` is the twisted class list of `RealLeviSlices`, `diag(κ) = blockDiagGL (sz dss) κ`,
`bdK (sz dss) κ` is the same matrix for `κ : ∀ i, unitaryCompact ℝ (sz dss i)`, and
`n̄(X) = lowerGL (sz dss) X`. `slots ds N`, `withModes`, `setMode`, `zeroModes` and `coeffs` are
as in `RealLeviDensity.md`. A list `J` of modes is **jointly allowed** for `S` if
`J.length = S.length` and `M ≤ |j|` at every slot of `withModes S J`. From `RealLeviModes`:
`IsNull S v` (all jointly allowed coefficients of `v` vanish on `O(N)`),
`symCoeffs L F` (the sum over the sign variants of the iterated coefficients, `symCoeffs_eq_sum`),
and `variants L` (the `2^{|L|}` lists obtained from `L` by flipping the signs of modes).
`RealLeviPairing.psi` and `RealLeviPairing.theta` are as in `RealLeviNonvanishing.md`:
`psi S u h κ X = coeffs (zeroModes S) (x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) 1` and
`theta S u h = ∫_{K_M} ∫_X psi S u h κ X dX dκ`, with
`K_M = ∏_i O(sz_i)` and the product `Measure.pi (fun i => haarK (sz dss i))` of the normalized
Haar measures.

## The statement

`RealLeviWitnessStatement`: assume `RealLeviChartIntegrableStatement`. Let `c : ℕ` and
`dss : Fin c → List RealBlock`, and write `ds = flat dss`. Assume

1. `realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p` for all positions `p ≤ q` in
   `Fin N`;
2. `realPositionBlockExponent ds q < realPositionBlockExponent ds p` for all positions with
   `cls (sz dss) p < cls (sz dss) q`;
3. for every `i`, the `O(sz_i)`-finite standard module of `cl dss i` is irreducible
   (`IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
   (realStandardLie (sz dss i) (cl dss i))`).

Then there are functions `φ_i` in `kFiniteFunctions (principalSeries ℝ (sz dss i)
(dualChar (realPositionCharacter (cl dss i)))) (unitaryCompact ℝ (sz dss i))` and a function
`h₀` in `kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)` with the following
property. Let `u` be in `kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter
ds))) (unitaryCompact ℝ N)`. Suppose that for all `Js : Fin c → List ℤ` such that each `Js i` is
jointly allowed for `slots (cl dss i) (sz dss i)`, and all `κ` with `κ_i ∈ O(sz_i)`,

`coeffs (withModes (slots ds N) (List.ofFn Js).flatten) u (diag(κ)) =
∏_i coeffs (withModes (slots (cl dss i) (sz dss i)) (Js i)) (φ_i) (κ_i)`.

Then

`∫_{K_M} ∫_{Coord (sz dss) → ℝ} c_Z(x ↦ u(x diag(κ)) h₀(x n̄(X) diag(κ))) dX dκ ≠ 0`,

where `c_Z F = coeffs (zeroModes (slots ds N)) F 1`. The double integral is
`RealLeviPairing.theta (slots ds N) u h₀`, the left side of the conclusion of
`RealLeviLimitStatement`. The hypotheses on `u` are the conclusion of `RealLeviDensityStatement`
for the same `φ_i`. Hypotheses 1 and 2 are those of `RealLeviLimitStatement`.

## Proof outline

1. **The standard module is nonzero** (`exists_std_ne_zero`). Every list `ds` of real blocks of
   rank `N` has a vector `x` in the `O(N)`-finite standard module with `x(1) ≠ 0`.
2. **Non-null dual vectors** (`exists_nonNull`). Apply step 1 to `cl dss i`, giving `x_i`. Let
   `φ_i` be the vector of the dual principal series that equals `conj x_i` on `O(sz_i)`. Then
   `φ_i` is not null along `slots (cl dss i) (sz dss i)`. So there are a jointly allowed `J_i`
   and `k_i ∈ O(sz_i)` with `coeffs (withModes (slots (cl dss i) (sz dss i)) J_i) φ_i k_i ≠ 0`.
3. **A density vector** (`realLeviDensity` with `W = ⊥`, which is proper by step 1). There is an
   `O(N)`-finite `u₀` in the dual principal series of `ds` whose jointly allowed coefficients at
   the points `diag(κ)` are the products of those of the `φ_i`.
4. **The test vector**. Let `J = (List.ofFn J_·).flatten` and `L₀ = withModes (slots ds N) J`.
   Then `J` is jointly allowed (`allowed_flat`). Let `f` be the vector of the principal series of
   `ds` that equals `conj (symCoeffs L₀ u₀)` on `O(N)`. Its block Fourier coefficients of modes
   `|m| ≠ |j|` at every slot of `L₀` vanish, so `f` lies in the standard module.
5. **Positivity at `X = 0`** (`psi_zero_eq`). `psi (slots ds N) u₀ f κ 0` is the sum over the
   sign variants `V` of `L₀` of `|coeffs V u₀ (diag(κ))|²`. This sum is a continuous nonnegative
   function `G` of `κ`. At `κ⁰ = (k_i)_i`, the variant `V = L₀` contributes
   `|∏_i coeffs (…) φ_i k_i|² > 0` by steps 2 and 3. Hence `∫_{K_M} G > 0`, and
   `∫_{K_M} psi (slots ds N) u₀ f κ 0 dκ ≠ 0`.
6. **Nonvanishing** (`RealLeviNonvanishing.exists_theta_ne_zero`). Some `O(N)`-finite `h₀` of the
   standard module has `Θ(u₀, h₀) ≠ 0`.
7. **Only the product coefficients matter** (`RealLeviPairing.theta_congr`). `Θ(u, h₀)` depends
   on `u` only through its jointly allowed coefficients at the points `diag(κ)`. These are the
   same for `u` and `u₀` when both have the product coefficients of the `φ_i`
   (`coeffs_eq_of_prodCoeffs`). Hence `Θ(u, h₀) = Θ(u₀, h₀) ≠ 0`.

## Results

**A nonzero vector of the standard module** (section `Nontrivial`).

* `entC k a b` is the entry `k_{ab}` as a complex number (`0` outside the range). `entP N a b` is
  the corresponding coordinate polynomial, and `eval_entP` evaluates it.
* `fac ds l k` is the factor at position `l`. If `realInducedBlockAt ds l = some d` (an
  induction block of weight `m = |d.weight|` starts at `l`), it is
  `(k_{ll} + i k_{l+1,l})^{m+1} + (k_{ll} - i k_{l+1,l})^{m+1}`. Otherwise it is `1` if
  `realPositionCharacter ds l (-1) = 1` and `k_{ll}` if not. `facP` is the same expression as a
  polynomial (`eval_facP`). `phiM ds k = ∏_{l < N} fac ds l k` and `phiP` is its polynomial
  (`eval_phiP`).
* Sign reflections: `entC_sign`, `fac_sign` and `phiM_sign`. With `ε_i` the diagonal sign
  reflection at `i`, `phiM ds (ε_i k) = realPositionCharacter ds i (-1) · phiM ds k`. At the first
  position `p` of an induction block of weight `m`, the character value is `(-1)^{m+1}`
  (`realInducedFirstCharacter`), and `fac` changes by this sign. At the second position `p + 1`,
  the character value is `1`, and `fac ds p` is invariant because the two summands are
  exchanged.
* Rotations: `entC_rot` gives the entries of `r_p(θ) k`, where `r_p(θ) = blockRotation N p θ`.
  `fac_rot_self`: at the first position `p` of an induction block of weight `m`,
  `fac ds p (r_p(θ) k) = e^{i(m+1)θ} A + e^{-i(m+1)θ} B`, with
  `A = (k_{pp} + i k_{p+1,p})^{m+1}` and `B = (k_{pp} - i k_{p+1,p})^{m+1}`.
  `fac_rot_ne`: the factors at the positions `l ≠ p` do not change. Such a factor is constant
  (`l = p + 1`, whose character value is `1`, gives the factor `1`) or involves only the rows
  `l` and `l + 1`, which are different from `p` and `p + 1`. `phiM_rot`: `θ ↦ phiM ds (r_p(θ) k)` is a combination of the
  Fourier modes `±(m + 1)` only.
* `fac_one_ne_zero` and `phiM_one_ne_zero`: `phiM ds 1 ≠ 0` (each factor is `2` or `1`).
* `exists_std_ne_zero`: if `realRank ds = N`, some
  `x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)` has `x 1 ≠ 0`. Proof:
  the restriction of `phiM ds` to `O(N)` is a polynomial in the matrix entries, so its right
  translates span a finite-dimensional space (`TranslateFinite.finiteDimensional_span_eval`). It
  transforms under the sign reflections by the position characters (`phiM_sign`,
  `apply_signDiagonal_mul`). Its extension `x` lies in the `O(N)`-finite principal series of the
  position characters (`PrincipalSeriesExtension.extension_mem_kFiniteFunctions`). At every slot
  of weight `m`, the block Fourier coefficients of `x` of modes `|j| < m` vanish on `O(N)`, by
  `phiM_rot` (only the modes `±(m+1)` occur). So `x` is in the standard module
  (`RealLeviModes.mem_kFin_standard_of_window`), and `x 1 = phiM ds 1 ≠ 0`.

**Non-null dual vectors** (section `NonNull`).

* `exists_nonNull`: if `realRank ds = N`, some `φ` in
  `kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
  (unitaryCompact ℝ N)` has a jointly allowed `J` for `slots ds N` and a `k ∈ O(N)` with
  `coeffs (withModes (slots ds N) J) φ k ≠ 0`. Proof: take `x` from `exists_std_ne_zero` and
  `φ` with `φ = conj x` on `O(N)` (`RealLeviModes.exists_ext_conj`). If `φ` were null,
  `integral_mul_eq_zero_of_mem_standard` would give `∫_{O(N)} |x|² = ∫_{O(N)} φ x = 0`. Then `x`
  would vanish on `O(N)` (`eq_zero_of_integral_norm_sq_eq_zero`, `x` continuous), contradicting
  `x 1 ≠ 0`.

**Sums of iterated coefficients** (section `Sums`).

* `ofReal_list_sum`: the coercion `ℝ → ℂ` commutes with list sums.
* `coeffs_list_sum`: `coeffs L` of a finite list sum of continuous functions is the sum of the
  `coeffs L`.
* `forall₂_withModes`: if `J.length = S.length`, then `withModes S J` and `S` have the same
  positions slot by slot.
* `map_zeroModes_of_forall₂`: two slot lists with the same positions slot by slot have the same
  `(position, mode)` data after `zeroModes`.

**The witness** (section `Witness`).

* `ProdCoeffs dss φ u`: for all jointly allowed `Js` and all `κ` with `κ_i ∈ O(sz_i)`, the
  coefficient of `u` along `withModes (slots (flat dss) N) (List.ofFn Js).flatten` at `diag(κ)` is
  `∏_i coeffs (withModes (slots (cl dss i) (sz dss i)) (Js i)) (φ_i) (κ_i)`. This is the
  hypothesis on `u` in the statement.
* `allowed_flat` and `allowed_split`: `(List.ofFn Js).flatten` is jointly allowed for
  `slots (flat dss) N` if and only if every `Js i` is jointly allowed for
  `slots (cl dss i) (sz dss i)`, when `Js i` has the right length (`RealLeviDensity.map_key3_flat`
  and `allowed_of_map_key3`).
* `coeffs_eq_of_prodCoeffs`: if `ProdCoeffs dss φ u` and `ProdCoeffs dss φ u'`, then `u` and `u'`
  have the same jointly allowed coefficients along `slots (flat dss) N` at every `bdK (sz dss) κ`.
  A jointly allowed `J` splits into `Js` (`RealLeviDensity.exists_split`).
* `psi_zero_eq`: let `u` be continuous, `J.length = (slots ds N).length` (`N = ∑_i sz_i`), and
  `f k = conj (symCoeffs (withModes (slots ds N) J) u k)` for `k ∈ O(N)`. Then
  `psi (slots ds N) u f κ 0 = ∑_{V ∈ variants (withModes (slots ds N) J)} |coeffs V u (bdK sz κ)|²`.
  Proof: `n̄(0) = 1` and right translation by `bdK sz κ` (`coeffs_mul_right`). `f` agrees with
  the sum `∑_V conj (coeffs V u)` on `O(N)` (`coeffs_congr_of_eqOn`, `symCoeffs_eq_sum`).
  Linearity (`coeffs_list_sum`) reduces to one variant `V`. Each variant has pairwise disjoint
  slots, and its zero-mode list has the same data as `zeroModes (slots ds N)`
  (`RealInducedTorusReduction.coeffs_congr_map`). For each `V`,
  `coeffs (zeroModes V) (y ↦ u y conj (coeffs V u y)) g = conj (coeffs V u g) · coeffs V u g`
  (`RealLeviModes.coeffs_zeroModes_mul_conj`, with `coeffs_blockRotation_mul` for the
  equivariance of `coeffs V u` along the rotations of the slots of `V`).
* `exists_witness`: steps 2–7 of the proof outline. Step 4 uses
  `RealLeviModes.symCoeffs_signReflection_mul`, `exists_ext_conj`,
  `exists_setMode_mem_withModes`, `blockFourierCoefficient_conj_symCoeffs_eq_zero` and
  `mem_kFin_standard_of_window`. The positivity in step 5 uses
  `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` for the product of the Haar
  probability measures on the compact group `K_M`.

`realLeviWitness` applies `exists_witness`. The integral in the statement is
`RealLeviPairing.theta (slots (flat dss) N) u h₀` unfolded.
