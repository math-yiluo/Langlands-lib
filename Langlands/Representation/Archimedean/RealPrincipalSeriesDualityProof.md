# Proof of `RealPrincipalSeriesDualityStatement`

Module: `Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof` (namespace
`Langlands.Archimedean.RealPrincipalSeriesDuality`).

Main theorem: `Langlands.Archimedean.RealPrincipalSeriesDuality.realPrincipalSeriesDuality :
Langlands.Archimedean.RealPrincipalSeriesDualityStatement`. The statement has no universe
parameters. The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

`RealPrincipalSeriesDualityStatement` is stated in
`Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction`. Fix `n` and two lists
`cs`, `cs'` of real characters (`RealCharacterData`). Write `χᵢ` and `χ'ᵢ` for the position
characters `realPositionCharacter (cs.map RealBlock.character) i` and
`realPositionCharacter (cs'.map RealBlock.character) i`, and assume `χᵢ(x) χ'ᵢ(x) = 1` for all
`i` and `x ∈ ℝˣ`. Let `I` and `I'` be the `O(n)`-finite functions (`kFiniteFunctions`) of the
standard modules `realStandardModule n (cs.map RealBlock.character)` and
`realStandardModule n (cs'.map RealBlock.character)`. The statement asks for a bilinear map
`Q : I × I' → ℂ` with three properties:

1. `Q(R(k) f, R(k) h) = Q(f, h)` for `k ∈ O(n)`, whenever both right translates again lie in
   `I` and `I'`;
2. `Q(R(X) f, h) + Q(f, R(X) h) = 0` for a real matrix `X`, whenever both right derivatives
   (`rightDerivative (matrixModel ℝ n) X`) again lie in `I` and `I'`;
3. for every `h ≠ 0` in `I'` there is `f ∈ I` with `Q(f, h) ≠ 0`.

The proof takes the integral over `O(n)` of the pointwise product:

`Q(f, h) = ∫_{O(n)} f(k) h(k) dk` (`pairing`),

with `dk` the normalized Haar measure on `O(n)`.

## Proof route

The classical argument writes the pairing as an integral over `B \ GL_n(ℝ)`, where `B` is the
upper triangular Borel subgroup. This proof avoids quotient measures. Invariance under `O(n)`
comes from right invariance of `dk`. Invariance under the Lie algebra comes from an
infinitesimal computation on `O(n)`. Nondegeneracy uses an explicit spherical vector.

### The Haar measure on `O(n)` (first section)

- `O(n)` is the Library subgroup `unitaryCompact ℝ n` of `GL_n(ℝ)`. It gets the Borel
  σ-algebra (local instances `measurableSpaceK`, `borelSpaceK`).
- `compactSpace_unitaryCompact`: `O(n)` is compact. The set `Matrix.unitaryGroup (Fin n) ℝ` is
  closed and bounded, so it is compact (`isCompact_unitaryGroup_set`), and it maps continuously
  onto `unitaryCompact ℝ n`.
- `haarK n` is `Measure.haarMeasure` normalized on the whole compact group. It is a
  probability measure.
- `isMulRightInvariant_haarK`: the measure is also right invariant. The right translate of
  `haarK n` is a left invariant measure, so by
  `Measure.isMulInvariant_eq_smul_of_compactSpace` it is a scalar multiple of `haarK n`. Both
  measures give the whole group mass `1`, so the scalar is `1`.
- `integrable_of_continuous`: continuous functions on `O(n)` are integrable.

### Integrals of left derivatives vanish

`integral_eq_zero_of_hasDerivAt_left`: let `γ` be a one-parameter subgroup of `O(n)`, and let
`Ψ` and `D` be continuous on `O(n)`. Assume `D(k)` is the derivative at `t = 0` of
`t ↦ Ψ(γ(t) k)`. Then `∫ D dk = 0`.

- By the group law, `D(γ(t) k)` is the derivative of `t ↦ Ψ(γ(t) k)` at every `t`.
- `D` is bounded on the compact group. So differentiation under the integral sign applies
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`): `t ↦ ∫ Ψ(γ(t) k) dk` has derivative
  `∫ D(γ(t) k) dk`.
- By left invariance (`integral_mul_left_eq_self`), that function is constant. So its derivative
  at `0`, which is `∫ D dk`, is `0`.

### Upper triangular directions (section `Upper`)

- `modulusExponent n i = n - 1 - 2i`.
- `IsModulusEquivariant φ`: `φ(exp(diag x) u g) = exp(∑ᵢ (n - 1 - 2i) xᵢ) φ(g)` for `u` upper
  unipotent. That is, `φ` transforms on the left under positive diagonal matrices and `N` by
  the modulus character of `B`.
- `fderiv_upperTriangular`: for smooth modulus-equivariant `φ` and upper triangular `U`, the
  derivative of `φ` at `k` in the direction `U k` is `(∑ᵢ (n - 1 - 2i) Uᵢᵢ) φ(k)`. Here `φ` is
  read through its extension `unitsExtension φ` to all matrices.
  - Split `U = Δ + N` into its diagonal `Δ` and its strictly upper part `N`.
  - The curve `Γ(t) = exp(tΔ)(1 + tN) k` has derivative `U k` at `0`. Along it,
    `φ(Γ(t)) = exp(t ∑ᵢ (n - 1 - 2i) Uᵢᵢ) φ(k)`.
  - The chain rule identifies the two derivatives (`congr_deriv`).

### Rotations (section `Rotation`)

- `rotGen a b = E_{ba} - E_{ab}` is antisymmetric. `expK W` is the one-parameter subgroup
  `t ↦ exp(tW)` of `O(n)` for antisymmetric `W`.
- `conjT X m = m X mᵀ`.
- `hasDerivAt_rotation`: for antisymmetric `W`, the derivative at `0` of
  `t ↦ (γ(t) X γ(t)ᵀ)_{ba} φ(γ(t))` with `γ(t) = exp(tW) k` is
  `(W S - S W)_{ba} φ(k) + S_{ba} dφ_k(W k)`, where `S = k X kᵀ`. This is the product rule
  together with `hasDerivAt_conjT_exp`.

### The integral of a right derivative (section `ModulusIntegral`)

`integral_rightDerivative_eq_zero`: if `φ` is smooth and modulus-equivariant, then
`∫_{O(n)} (R(X) φ)(k) dk = 0` for every real matrix `X`.

- At `k ∈ O(n)`, `R(X)φ(k) = dφ_k(k X)` (`rightDerivative_eq_fderiv`), and
  `k X = S k` with `S = k X kᵀ`, because `kᵀ k = 1`.
- Write `S = (S - R) + R` with `R = ∑_{a<b} S_{ba} (E_{ba} - E_{ab})` (`rotSum_eq`).
  `S - R` is upper triangular with the same diagonal as `S` (`isUpperTriangular_sub_rotSum`,
  `sub_rotSum_apply_self`).
- So `fderiv_upperTriangular` gives
  `R(X)φ(k) = (∑ᵢ (n - 1 - 2i) Sᵢᵢ) φ(k) + ∑_{a<b} S_{ba} dφ_k(W_{ab} k)`, with
  `W_{ab} = E_{ba} - E_{ab}`.
- One computes `(W_{ab} S - S W_{ab})_{ba} = S_{aa} - S_{bb}` (`rotGen_comm_apply`).
  Also `∑ᵢ (n - 1 - 2i) xᵢ = ∑_{a<b} (x_a - x_b)` (`sum_modulusExponent`).
  Together these give `rightDerivative_eq_sum_rotationTerm`: pointwise on `O(n)`, `R(X)φ` is
  the sum over `a < b` of the terms `rotationTerm φ X a b`, where
  `rotationTerm φ X a b k = (W_{ab} S - S W_{ab})_{ba} φ(k) + S_{ba} dφ_k(W_{ab} k)`.
- By `hasDerivAt_rotation`, each `rotationTerm φ X a b` is the left derivative along
  `exp(t W_{ab})` of `k ↦ (k X kᵀ)_{ba} φ(k)`. Each term is continuous
  (`continuous_rotationTerm`), so its integral vanishes by
  `integral_eq_zero_of_hasDerivAt_left` (`integral_rotationTerm`). Summing the finitely many
  terms (`integral_finsetSum`) gives the claim.

### Products (section `Products`)

- `contMDiff_mul_fun` and `rightDerivative_mul_fun`: products of smooth functions on `GL_n(ℝ)`
  are smooth, and `R(X)` satisfies the product rule.
- `isModulusEquivariant_mul`: if `f` lies in `principalSeries ℝ n χ`, `h` lies in
  `principalSeries ℝ n χ'`, and `χᵢ χ'ᵢ = 1`, then `f h` is modulus-equivariant. The two
  characters `principalSeriesCharacter` multiply, at `exp(diag x)`, to
  `∏ᵢ exp(xᵢ)^{n - 1 - 2i}`. The positive diagonal unit `exp(diag x)` is rewritten as
  `Iwasawa.diagonalUnits` (`matrixExpUnit_diagonal`).

### The pairing (section `Pairing`)

These results hold for arbitrary lists of real blocks `ds`, `ds'`.

- `pairing n ds ds'`: the bilinear map `(f, h) ↦ ∫_{O(n)} f(k) h(k) dk`. The functions are
  continuous because they are smooth (`contMDiff_of_mem_realStandardModule`), so the integrand
  is integrable.
- `pairing_rightTranslation` (property 1): right invariance of `haarK n`
  (`integral_mul_right_eq_self`).
- `pairing_rightDerivative` (property 2), assuming the position characters are pointwise
  inverse:
  - `f` and `h` lie in their principal series (`realStandardModule_le_principalSeries`).
  - So `f h` is smooth and modulus-equivariant.
  - By the product rule, `R(X)f · h + f · R(X)h = R(X)(f h)`. Its integral over `O(n)` is `0`
    by `integral_rightDerivative_eq_zero`.

### A spherical vector (sections `Spherical` and `SphericalGL`)

For a real vector `r`, the proof builds a smooth function `φ_r` on `GL_n(ℝ)` with three
properties: `φ_r(diag(a) u g) = ∏ⱼ |aⱼ|^{rⱼ} φ_r(g)` for `u` upper unipotent,
`φ_r(g k) = φ_r(g)` for `k ∈ O(n)`, and `φ_r = 1` on `O(n)`.

- `tailProj n m` and `headProj n m` are the diagonal projections onto the coordinates `i ≥ m`
  and `i < m`. `paddedGram m y = D_m y yᵀ D_m + (1 - D_m)`, with `D_m = tailProj n m`. Its
  determinant `minorDet m y` is the Gram determinant of the rows `i ≥ m` of `y`.
- `minorDet m (y k) = minorDet m y` for `k kᵀ = 1`, and `minorDet m k = 1`
  (`minorDet_mul_orth`, `minorDet_orth`).
- `minorDet_upper_mul`: for upper triangular `c`,
  `minorDet m (c y) = (∏_{i ≥ m} cᵢᵢ)² minorDet m y`. The proof factors
  `paddedGram m (c y) = B (paddedGram m y) Bᵀ` with `B = D_m c D_m + (1 - D_m)`
  (`paddedGram_upper_mul`, using `D_m c = D_m c D_m` for upper triangular `c`), and
  `det B = ∏_{i ≥ m} cᵢᵢ` (`det_blockFactor`).
- `minorDet_pos`: `minorDet m y > 0` for invertible `y`. Write `y = b u` with `b` upper
  triangular and `u` orthogonal. This is the Library's
  `Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary`.
- `sphericalReal r y = ∏ⱼ (minorDet j y / minorDet (j+1) y)^{rⱼ/2}`. It is smooth on the
  invertible matrices (`contDiffOn_sphericalReal`): the Gram determinants are polynomial
  (`contDiff_minorDet`) and positive there. It is right `O(n)`-invariant, equal to `1` on
  `O(n)`, and satisfies `sphericalReal r (c y) = ∏ⱼ |cⱼⱼ|^{rⱼ} sphericalReal r y` for upper
  triangular invertible `c` (`sphericalReal_upper_mul`, from `minorDet_upper_mul` and
  `prod_tail_succ`).
- `spherical r g` is `sphericalReal r g` viewed in `ℂ`. Its lemmas are `contMDiff_spherical`,
  `spherical_mul_mem`, `spherical_mem` and `spherical_diagonal_mul`.

### Nondegeneracy (section `Nondegeneracy`)

- `norm_character` and `exists_norm_realPositionCharacter`: every position character of a list
  of real characters satisfies `|χ'ᵢ(x)| = |x|^{σᵢ}` for some real `σᵢ`. For a real character
  with exponent `s`, `σ = Re s`; positions beyond the list carry the trivial character.
- `realInducedBlockAt_map_character`: a list of real characters has no induction blocks. So
  membership in `realStandardModule` is membership in the principal series of the position
  characters.
- `principalSeriesCharacter_conj_mul` (from `conj_mul_rpow`): if `χᵢ χ'ᵢ = 1` and
  `|χ'ᵢ(x)| = |x|^{σᵢ}`, then the conjugate of the `χ'` character times `∏ⱼ |aⱼ|^{-2σⱼ}` is the
  `χ` character.
- `conjMulSpherical r v = conj(v) · φ_r`, a conjugate-linear map.
  - `conjMulSpherical_mem_principalSeries`: with `r = -2σ`, it maps the principal series of `χ'`
    into that of `χ`.
  - It commutes with right translation by `O(n)` (`conjMulSpherical_rightTranslation`).
  - So it maps `O(n)`-finite functions to `O(n)`-finite functions
    (`conjMulSpherical_mem_kFiniteVectors`): the span of the translates of `conj(v) φ_r` is the
    image of the finite-dimensional span of the translates of `v`.
- `exists_mem_unitaryCompact_ne_zero`: a nonzero function of a principal series is nonzero at
  some point of `O(n)`. Write `g = diag(bᵢᵢ) · u' · k` with `u'` upper unipotent and `k`
  orthogonal, using `exists_upperTriangular_mul_unitary`, and apply the transformation law.
- `exists_pairing_ne_zero` (property 3): for `h ≠ 0` in `I'`, take `f = conj(h) φ_{-2σ} ∈ I`.
  On `O(n)`, `φ_{-2σ} = 1`, so `Q(f, h) = ∫_{O(n)} |h(k)|² dk`. The integrand is continuous,
  nonnegative, and nonzero at some point of `O(n)`, and Haar measure charges open sets. So the
  integral is positive (`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`).

### The theorem

`realPrincipalSeriesDuality` takes `Q = pairing n (cs.map RealBlock.character)
(cs'.map RealBlock.character)`. The three properties are `pairing_rightTranslation`,
`pairing_rightDerivative` and `exists_pairing_ne_zero`.

## Dependencies

Library modules:

- `Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction`: the statement.
- `Langlands.Representation.Archimedean.RealStandardModuleFourier`: `matrixExpUnit` and
  `realStandardModule_le_principalSeries`.
- `Langlands.Representation.Archimedean.RealStandardModuleGKModule`:
  `contMDiff_of_mem_realStandardModule`.
- `Langlands.Representation.Archimedean.PrincipalSeriesStability`: `unitsExtension`,
  `rightDerivative_eq_fderiv`, `contMDiff_of_contDiffOn`.
- `Langlands.LinearAlgebra.TriangularUnitary`: the decomposition `y = b u`.

Mathlib: Haar measure, differentiation under the integral sign, the matrix exponential, and
matrix determinants.
