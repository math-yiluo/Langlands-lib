# Explicit `GL_3(ℝ)` matrices for the landing integrals

Lean module: `Langlands.Representation.Archimedean.RealSwapLandingMatrices`, namespace
`Langlands.Archimedean.RealSwapLandingMatrices`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. It collects the
explicit matrix computations in `GL_3(ℝ)` behind the hypothesis `SpecialLanding` of the module
`RealSwapLandingAlgebra`:

- named elements of `GL_3(ℝ)` (lower unipotents, permutations, upper triangular matrices) and
  the identities between them, the rotations `r_0(θ)`, `r_1(θ)` and the chart `chartGL`;
- the values of the principal series character of the blocks
  `[induced d, character (charData e s)]` at two diagonal matrices;
- the rank-one transformation laws that `RealSwapLandingRankOne.integral_eq_kernelOp` needs,
  for a function `f` of that principal series and for its kernel transform `C¹_n f`.

All identities are elementary matrix computations. The module formalizes no literature
statement, so it has no sources. All declarations are auxiliary definitions and lemmas proved
here from Mathlib and Library results.

## Notation

- `GL_3(ℝ)` is `Langlands.GeneralLinear 3 ℝ`. Matrices are written by rows.
- `r_p(θ) = blockRotation 3 p θ` is the rotation in the coordinates `p, p + 1`
  (`RealBlockRotation`). Write `C = cos θ`, `S = sin θ`.
- `chartGL v` (`MaximalParabolicIntegration`) is the lower unipotent matrix with last row
  `(v₀, v₁, 1)`.
- `C^r_p F (g) = kernelOp 3 p r F g = ∫₀^π sin^r θ F(r_p(θ) g) dθ` (`RealSwapLandingKernel`).
- `cotan θ = cos θ / sin θ` (`RealSwapLandingRankOne`).
- `ℓ = |m|` is `d.weight.natAbs` and `t` is `d.exponent` for complex character data `d`.
- `charFun e s x = sgn(x)^e |x|^s` and `charData e s` are the real characters of
  `RealJacquetFrobenius` (Library module `RealJacquetFrobeniusProof`).

## Declarations

### Elements of `GL_3(ℝ)`

- `glOf M h`: the `3 × 3` real matrix `M` with `det M ≠ 0`, as an element of `GL_3(ℝ)`.
  `glOf_val`: its underlying matrix is `M`.
- `nbar0 y = [[1,0,0],[y,1,0],[0,0,1]]`, `nbar1 y = [[1,0,0],[0,1,0],[0,y,1]]`.
- `s0 = [[0,1,0],[1,0,0],[0,0,1]]`, `s1 = [[1,0,0],[0,0,1],[0,1,0]]` (transpositions).
- `wPerm = [[0,1,0],[0,0,1],[1,0,0]]`. `wPerm_mem_unitaryCompact`: it lies in `O(3)`.
- `upper3 a b c x y z = [[a,x,y],[0,b,z],[0,0,c]]` for units `a, b, c ∈ ℝˣ` and `x, y, z ∈ ℝ`.

### The rotations and the chart

- `rot0_val`: `r_0(θ) = [[C,-S,0],[S,C,0],[0,0,1]]`.
- `rot1_val`: `r_1(θ) = [[1,0,0],[0,C,-S],[0,S,C]]`.
- `chartGL_val`: `chartGL v = [[1,0,0],[0,1,0],[v₀,v₁,1]]`.

### Matrix identities

Each identity is proved entrywise; the entries need `S² + C² = 1` and, where `S⁻¹` occurs,
`S ≠ 0`.

- `chartGL_mul_wPerm`: `chartGL v · w = n̄₁(v₁) s₁ · n̄₀(v₀) s₀`.
- `wPerm_mul_rot1`: `w r_1(θ) = r_0(θ) w`.
- `rotInv θ = [[C,S],[-S,C]]`, the rotation by `-θ` acting on row vectors. `det_rotInv`: its
  determinant is `1`.
- `rot0_mul_chartGL`: `r_0(θ) · chartGL v = chartGL (v · rotInv θ) · r_0(θ)`, with `v` a row
  vector (`v ᵥ* rotInv θ`).
- `nbar1_cotan` (for `S ≠ 0`): `n̄₁(cot θ) s₁ = upper3 1 (-S) S⁻¹ 0 0 C · r_1(θ)`.
- `nbar0_cotan` (for `S ≠ 0`): `n̄₀(cot θ) s₀ = upper3 (-S) S⁻¹ 1 C 0 0 · r_0(θ)`.
- `nbar1_s1_upper3` (for `S ≠ 0` and all `C, y ∈ ℝ`):
  `n̄₁(y) s₁ · upper3 (-S) S⁻¹ 1 C 0 0 = upper3 (-S) 1 S⁻¹ (-C y S) C 0 · n̄₁(y S) s₁`.

### Upper triangular left translations in the principal series of `GL_3(ℝ)`

- `upper3_blockTriangular`: `upper3 a b c x y z` is upper triangular
  (`Matrix.BlockTriangular id`).
- `mul_upper3`: for `f ∈ principalSeries ℝ 3 χ`,
  `f(upper3 a b c x y z · g) = principalSeriesCharacter ℝ 3 χ ![a, b, c] · f(g)`. This is
  `RealSwapLandingRankOne.mul_of_upperTriangular` for this matrix.
- `principalSeriesCharacter_three`: the Library character
  `∏ᵢ χᵢ(aᵢ) |aᵢ|^((3-1)/2 - i)` equals
  `χ₀(a₀) |a₀| · χ₁(a₁) · χ₂(a₂) |a₂|⁻¹`, since the exponents are `1, 0, -1` and `[ℝ : ℝ] = 1`.

### The characters of `[induced d, character (charData e s)]`

- `posChar d e s` is `realPositionCharacter [RealBlock.induced d, RealBlock.character
  (charData e s)]`. `posChar_zero`, `posChar_one`, `posChar_two`: its values at positions
  `0, 1, 2` are `realInducedFirstCharacter d` (`x ↦ sgn(x)^{ℓ+1} |x|^{t+ℓ/2}`),
  `realInducedSecondCharacter d` (`x ↦ |x|^{t-ℓ/2}`) and `charFun e s`.
- `ofReal_inv_cpow`: for `S > 0` and `z ∈ ℂ`, `(S⁻¹)^z = S^{-z}`, since the argument of a
  positive real number is `0 ≠ π`.
- `charFun_inv`: for `S > 0`, `charFun e s (S⁻¹) = S^{-s}`.
- `principalSeriesCharacter_block1`: for `S > 0` and `s = t - ℓ/2 - (n + 1)`, the character
  `principalSeriesCharacter ℝ 3 (posChar d e s)` at `(1, -S, S⁻¹)` is `S^{n+2}`. Its value is
  `1 · 1 · S^{t-ℓ/2} · S^{-s} · S = S^{t-ℓ/2-s+1}`.
- `principalSeriesCharacter_block0`: under the same hypotheses its value at `(-S, 1, S⁻¹)` is
  `(-1)^{ℓ+1} S^{n+ℓ+3}`. The value is
  `(-1)^{ℓ+1} S^{t+ℓ/2} · S · 1 · S^{-s} · S = (-1)^{ℓ+1} S^{t+ℓ/2-s+2}`.

### The rank-one transformation laws

Fix `d`, `e`, `n ∈ ℕ` and `s = t - ℓ/2 - (n + 1)`, and let
`f ∈ principalSeries ℝ 3 (posChar d e s)`.

- `principalSeries_nbar1_cotan`: for `θ ∈ (0, π)` and every `x`,
  `f(n̄₁(cot θ) s₁ x) = 1 · sin^{n+2} θ · f(r_1(θ) x)`. Proof: `nbar1_cotan`, `mul_upper3` and
  `principalSeriesCharacter_block1` with `S = sin θ > 0`.
- `integral_nbar1`: for every `g`, `∫_ℝ f(n̄₁(y) s₁ g) dy = C¹_n f (g)`. This is
  `RealSwapLandingRankOne.integral_eq_kernelOp` with `p = 1`, `r = n`, `σ = 1`.
- `kernelOp_nbar0_cotan`: for `θ ∈ (0, π)` and every `x`,
  `C¹_n f(n̄₀(cot θ) s₀ x) = (-1)^{ℓ+1} sin^{n+ℓ+2} θ · C¹_n f(r_0(θ) x)`.
  Proof: let `S = sin θ`, `B = upper3 (-S) S⁻¹ 1 C 0 0` and `X = r_0(θ) x`. By `nbar0_cotan`,
  `n̄₀(cot θ) s₀ x = B X`. By `integral_nbar1` on both sides, the claim is an identity of the
  integrals `∫_ℝ f(n̄₁(y) s₁ B X) dy` and `∫_ℝ f(n̄₁(y) s₁ X) dy`. By `nbar1_s1_upper3` and
  `mul_upper3`, `f(n̄₁(y) s₁ B X) = (-1)^{ℓ+1} S^{n+ℓ+3} f(n̄₁(y S) s₁ X)`; the character value is
  `principalSeriesCharacter_block0` and does not depend on `y`. The substitution `y ↦ y S`
  (Mathlib's `Measure.integral_comp_mul_right`) contributes the factor `|S⁻¹| = S⁻¹`. This
  holds as an equality of Bochner integrals, with no integrability hypothesis.
