# The dual step along `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`: orthogonality passes to `GL_a(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockDual`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It is
the recursion step of the Langlands-quotient argument along the maximal parabolic subgroup
`P_{a,k+1}` whose last block is tied. It generalizes the induction step of the published
`JacquetDual.jacquet_eq_zero` (`P_{m,1}`), where the restriction `u ↦ u ∘ ι` suffices. Here the
tied `GL_{k+1}(ℝ)` factor is passive: Jacobson density on its irreducible principal series
(`GKModuleDensity`) replaces `u(diag(κ₁, κ₂))` by `u(diag(κ₁, 1)) φ(κ₂)`. The module is the real
analogue of Worker 140's `ComplexBlockDual` (Task 7063) and follows its structure.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is `unitaryCompact ℝ N`, with the
Haar probability measure `RealPrincipalSeriesDuality.haarK N`. `n̄(X)`, `diag(g₁, g₂)`
(`blockLowerGL`, `blockDiagGL`) and the matrix `RealBlockParabolic.blockDiag` come from
`RealBlockParabolicIntegrationStatement`. `blockStep`, `blockPair`, `blockShiftChar` and
`IsBlockDominant` come from `RealBlockJacquet`, and `integral_mul_blockStep_eq_zero` and
`blockDiagGL_mem_unitaryCompact` from `RealBlockLimit`. `IsSignedPower χ e` (module
`PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`, and `dualChar χ = (l, x) ↦ (χ_l x)⁻¹` (module `JacquetLimit`).
`principalSeriesRep`, `principalSeriesLie`, `kFiniteEval`, `kFiniteRep_isFiniteVector`,
`kFiniteRep_continuous` (`PrincipalSeriesGKModule`), `isAdmissibleGKModule_kFiniteRep`,
`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact` (`RealStandardModuleAdmissible`) and
`IsIrreducibleGKModule` (`GKModule`) are the Library's. Unprefixed names below are in the
namespace `Langlands.Archimedean.RealBlockDual`.

## The statement

`RealBlockDualStatement` assumes the two statements `RealBlockChartIntegrableStatement` and
`RealBlockParabolicIntegrationStatement`. These are only stated, not yet proved, in the Library.
Under these assumptions it says the following.

Let `χ` be signed-power characters with exponents `e`, that is
`χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and `‖χ_l(−1)‖ = 1`, such that

* `Re e_{l+1} ≤ Re e_l` for `l < a`,
* `Re e_a < Re e_{a−1}` (when `a ≥ 1`), and
* `Re e_a = ⋯ = Re e_{a+k}`.

Let `χT` be characters with `χT_l(x) = χ_{a+l}(x)⁻¹ |x|^{-a/2}` for `l ≤ k`, such that the
`(𝔤𝔩_{k+1}(ℝ), O(k+1))`-module `(principalSeriesRep ℝ (k+1) χT, principalSeriesLie ℝ (k+1) χT)` is
irreducible.

Let `U` be a subspace of the `O(a+k+1)`-finite functions of `principalSeries ℝ (a+k+1) χ⁻¹`,
stable under right translation by `O(a+k+1)` and under all right derivatives. Let `h` be an
`O(a+k+1)`-finite function of `principalSeries ℝ (a+k+1) χ` with `∫_{O(a+k+1)} u h = 0` for every
`u ∈ U`. Then for every `O(k+1)`-finite `φ` of `principalSeries ℝ (k+1) χT` and every `u ∈ U`,

`∫_{O(a)} u(diag(κ₁, 1)) · blockPair φ h (κ₁) dκ₁ = 0`, where
`blockPair φ h (κ₁) = ∫_{O(k+1)} φ(κ₂) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂`.

It is proved as `Langlands.Archimedean.realBlockDual`, from
`integral_restrictBlock_mul_blockPair_eq_zero`. In the recursion, the irreducibility hypothesis
is to be supplied by `RealTemperedStandardIrreducibleStatement`: the characters `χT` have equal
real parts of exponents.

Provenance. Derived, internal infrastructure: the inductive step of the leading-term argument for
the Langlands quotient along a maximal parabolic subgroup whose Levi block is tempered up to a
twist. No literature statement is claimed.

## Proof

### Affine embeddings (section `Embed`)

Let `ι : GL_m(ℝ) → GL_N(ℝ)` be given on matrices by `Y ↦ L Y + C` with `L` continuous and linear.

* `contMDiff_comp_affine`: `x ↦ u(c ι(x))` is smooth for smooth `u`. In matrix coordinates it is
  `unitsExtension u ∘ (Y ↦ c (L Y + C))`, which maps invertible matrices to invertible matrices.
* `rightDerivative_comp_affine`: if also `L(g Y) = ι(g) L(Y)`, then
  `R(Y)(u(c ι(·)))(g) = (R(L Y) u)(c ι(g))`. The proof uses `rightDerivative_eq_fderiv` and the
  chain rule for the affine map, whose derivative is `W ↦ c L W`.

### Block embeddings (section `Block`)

* `blockDiag_add`, `blockDiag_smul`, `blockDiag_mul`: `diag(A, D)` is additive, homogeneous and
  multiplicative.
* `leftLin A = diag(A, 0)` and `rightLin D = diag(0, D)` are continuous linear maps
  (`leftLin_apply`, `rightLin_apply`).
* `blockDiagGL_left_val`, `blockDiagGL_right_val`: `diag(g, 1) = leftLin g + diag(0, 1)` and
  `diag(1, g) = rightLin g + diag(1, 0)`.
* `leftLin_mul`, `rightLin_mul`: the compatibility `L(g Y) = ι(g) L(Y)`.
* `blockDiagGL_one_one`: `diag(1, 1) = 1`. `blockDiagGL_eq_mul`:
  `diag(g₁, g₂) = diag(g₁, 1) diag(1, g₂)`.
* `blockDiagGL_diagonalUnits_right`, `blockDiagGL_mem_upperUnipotent_right`: the counterparts of
  `RealBlockJacquet.blockDiagGL_diagonalUnits` and `RealBlockJacquet.blockDiagGL_mem_upperUnipotent`
  for the second block.

### Restriction and slices (section `Restrict`)

* `restrictBlock u (g₁) = u(diag(g₁, 1))` and `sliceFun κ₁ u (g₂) = u(diag(κ₁, g₂))` are linear
  maps (`restrictBlock_apply`, `sliceFun_apply`).
* `blockDualChar a χ l x = χ_{a+l}(x)⁻¹ |x|^{-a/2}`.
* Smoothness and derivatives: `contMDiff_restrictBlock`, `rightDerivative_restrictBlock`
  (`R(Y) ∘ restrictBlock = restrictBlock ∘ R(diag(Y, 0))`), `contMDiff_sliceFun`,
  `rightDerivative_sliceFun` (`R(Y) ∘ sliceFun κ₁ = sliceFun κ₁ ∘ R(diag(0, Y))`). These come from
  the affine-embedding lemmas, using `sliceFun_eq`: `u(diag(κ₁, g₂)) = u(diag(κ₁, 1) diag(1, g₂))`.
* Translations: `rightTranslation_restrictBlock`, `rightTranslation_sliceFun`, and
  `sliceFun_eq_sliceFun_one`: `sliceFun κ₁ u = sliceFun 1 (R(diag(κ₁, 1)) u)`.
* Characters: `principalSeriesCharacter_addCases_dual` says the character of `χ⁻¹` on
  `GL_{a+k+1}(ℝ)` at `(z, 1, …, 1)` is the `GL_a` character of `(blockShiftChar k χ)⁻¹` at `z`.
  `principalSeriesCharacter_addCases_right_dual` says the character of `χ⁻¹` at `(1, …, 1, z)` is
  the `GL_{k+1}` character of `blockDualChar a χ` at `z`: the modulus exponent at position `a+i`
  is `(a+k)/2 − (a+i)`, which is `k/2 − i` plus `−a/2`. Both follow by comparing factors.
* `restrictBlock_mem`: `restrictBlock u` is an `O(a)`-finite function of the principal series of
  `(blockShiftChar k χ)⁻¹`.
* `sliceFun_mem`: `sliceFun κ₁ u` is an `O(k+1)`-finite function of the principal series of `χT`.
  For an `O(a+k+1)`-finite `u` of the principal series of `χ⁻¹`, equivariance follows from
  `diag(κ₁, b g₂) = diag(1, b) diag(κ₁, g₂)` and the character lemmas. Finiteness follows because
  the translates of the restricted function are restrictions of translates of `u`.

### Density on the tied block (section `Density`)

* `hyp_principalSeries`: an irreducible real principal series satisfies `GKModuleDensity.Hyp`.
  Admissibility is the Library's `isAdmissibleGKModule_kFiniteRep`, applied to the principal
  series itself (stable under right translation by `rightTranslation_mem_principalSeries`). Every
  vector lies in its finite-dimensional orbit span (`kFiniteRep_isFiniteVector`,
  `FiniteVectors.orbitSubrepresentation`). Matrix coefficients are continuous
  (`kFiniteRep_continuous`).
* `sliceV κ₁ u` is `sliceFun κ₁ u` as an element of the `O(k+1)`-finite principal series of `χT`
  (`sliceV_coe`, `sliceV_add`, `sliceV_smul`).
* `exists_sliceV_eq`: for every element `A` of the free algebra on
  `O(k+1) ⊕ (ℂ ⊗_ℝ 𝔤𝔩_{k+1}(ℝ))` and every `u ∈ U`, some `u' ∈ U` satisfies
  `sliceV κ₁ u' = A · sliceV κ₁ u` for all `κ₁` at once. Here `A` acts through
  `FreeAlgebra.lift` of `GKModuleDensity.gens`. The proof is by induction on `A`:
  * scalars give `r • u`;
  * the generator `κ₂` gives `R(diag(1, κ₂)) u` (`rightTranslation_sliceFun`);
  * the generator `z ⊗ Y = z • (1 ⊗ Y)` gives `z • R(diag(0, Y)) u` (`rightDerivative_sliceFun`,
    `principalSeriesLie_one_tmul_apply_coe`); sums of tensors are handled by additivity;
  * products compose the witnesses;
  * sums add them.

### The dual step (section `Step`)

`integral_restrictBlock_mul_blockPair_eq_zero`. Fix `u ∈ U`.

1. All slices `sliceV κ₁ u` (`κ₁ ∈ O(a)`) lie in the finite-dimensional space `S`. `S` is the
   preimage of the image under `sliceFun 1` of the span of the `O(a+k+1)`-translates of `u`
   (`sliceFun_eq_sliceFun_one`, `blockDiagGL_mem_unitaryCompact`).
2. Take a finite spanning set of `S` (`Submodule.fg_iff_finiteDimensional`) and the rank-one map
   `f(v) = v(1) · φ` (`kFiniteEval`, `LinearMap.smulRight`).
3. `GKModuleDensity.exists_freeAlgebra_eq` (with `hyp_principalSeries`) gives `A` agreeing with `f`
   on the spanning set, hence on `S` (`LinearMap.eqOn_span`).
4. `exists_sliceV_eq` gives `u' ∈ U` with `u'(diag(κ₁, κ₂)) = u(diag(κ₁, 1)) φ(κ₂)` for
   `κ₁ ∈ O(a)`, `κ₂ ∈ O(k+1)`.
5. By orthogonality invariance (`JacquetDual.integral_mul_eq_zero_of_orthogonal`),
   `∫_{O(a+k+1)} u'(κ g) h(κ) dκ = 0` for every `g`.
6. The block limit `RealBlockLimit.integral_mul_blockStep_eq_zero` for `u'` gives
   `0 = ∫∫ u'(diag(κ₁, κ₂)) blockStep h (diag(κ₁, κ₂)) = ∫ u(diag(κ₁, 1)) blockPair φ h (κ₁)`.

`map_restrictBlock` holds for nonzero `U` and is not part of the statement. It says that
`U.map restrictBlock` is a nonzero subspace of the `O(a)`-finite principal series of
`(blockShiftChar k χ)⁻¹`, stable under right translation by `O(a)` and under right derivatives.
Nonvanishing follows by translating a `u` with `u(κ) ≠ 0` (it exists by
`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`) and evaluating at `1`. This is the input
of the next step of the recursion on `GL_a(ℝ)`.
