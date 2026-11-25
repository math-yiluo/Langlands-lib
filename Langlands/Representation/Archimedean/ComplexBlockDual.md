# The dual step along `P_{a,k+1}`: orthogonality passes to `GL_a(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockDual`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the recursion step of the Langlands-quotient
argument along `P_{a,k+1}` with a tied last block. It generalizes the induction step of the
published `ComplexJacquetDual.jacquet_eq_zero` (`P_{m,1}`). There the restriction `u ↦ u ∘ ι`
suffices. Here the tied `GL_{k+1}(ℂ)` factor is passive: Jacobson density on its irreducible
principal series (`GKModuleDensity`) replaces `u(diag(κ₁, κ₂))` by `u(diag(κ₁, 1)) φ(κ₂)`.

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ`, `U(N)` is `unitaryCompact ℂ N` with Haar
probability measure `unitaryHaar N`, and `n̄(X)`, `diag(g₁, g₂)` (`blockLowerGL`, `blockDiagGL`,
`ComplexBlockParabolic.blockDiag`) come from `ComplexBlockParabolicIntegrationStatement`.
`blockStep`, `blockPair`, `blockShiftChar` and `IsBlockDominant` come from `ComplexBlockJacquet`,
and `integral_mul_blockStep_eq_zero` from `ComplexBlockLimit`. `principalSeriesRep`,
`principalSeriesLie` (`PrincipalSeriesGKModule`), `IsIrreducibleGKModule`, `IsAdmissibleGKModule`
and `gkIntertwiners` (`GKModule`) are the Library's. `dualChar χ = (l, z) ↦ (χ_l z)⁻¹`.
Unprefixed names below are in the namespace `Langlands.Archimedean.ComplexBlockDual`.

## The statement

`ComplexBlockDualStatement` assumes the two statements `ComplexBlockChartIntegrableStatement` and
`ComplexBlockParabolicIntegrationStatement`. Both are proved in the Library
(`complexBlockChartIntegrable`, `complexBlockParabolicIntegration`). Under these assumptions it says the following.

Let `χ` be phase-power characters with exponents `e` such that

* `Re e_{l+1} ≤ Re e_l` for `l < a`,
* `Re e_a < Re e_{a−1}` (when `a ≥ 1`), and
* `Re e_a = ⋯ = Re e_{a+k}`.

Let `χT` be characters with `χT_l(z) = χ_{a+l}(z)⁻¹ (|z|²)^{-a/2}` for `l ≤ k`, such that the
`(𝔤𝔩_{k+1}(ℂ), U(k+1))`-module `(principalSeriesRep ℂ (k+1) χT, principalSeriesLie ℂ (k+1) χT)` is
irreducible.

Let `U` be a subspace of the `U(a+k+1)`-finite functions of `principalSeries ℂ (a+k+1) χ⁻¹`,
stable under right translation by `U(a+k+1)` and under all right derivatives. Let `h` be a
`U(a+k+1)`-finite function of `principalSeries ℂ (a+k+1) χ` with `∫_{U(a+k+1)} u h = 0` for
every `u ∈ U`. Then for every `U(k+1)`-finite `φ` of `principalSeries ℂ (k+1) χT` and every
`u ∈ U`,

`∫_{U(a)} u(diag(κ₁, 1)) · blockPair φ h (κ₁) dκ₁ = 0`, where
`blockPair φ h (κ₁) = ∫_{U(k+1)} φ(κ₂) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂`.

It is proved as `Langlands.Archimedean.complexBlockDual`, from
`integral_restrictBlock_mul_blockPair_eq_zero`. In the recursion, the irreducibility hypothesis
is supplied by `ComplexTemperedStandardIrreducibleStatement`: the characters `χT` have equal
real parts of exponents.

Provenance. Derived, internal infrastructure: the inductive step of the leading-term argument for
the Langlands quotient along a maximal parabolic subgroup whose Levi block is tempered up to a
twist. No literature statement is claimed.

## Proof

### Admissibility (section `Admissible`)

`isAdmissibleGKModule_kFiniteRep`: the `U(n)`-finite functions of a right-translation-stable
subspace `V` of a complex principal series form an admissible representation of `U(n)`. A
`K`-intertwiner `T` from a matrix representation `τ` is determined by the functional
`valueAtOne T : x ↦ (T x)(1)`:

* `intertwiner_apply_unitary` gives `(T x)(κ) = (T(τ(κ) x))(1)`;
* principal-series functions are determined by their values on `U(n)`
  (`ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary`), so `valueAtOne` is injective
  (`valueAtOne_injective`);
* hence `gkIntertwiners` is finite-dimensional.

This is the complex analogue of the Library's `RealStandardModuleAdmissible`.

### Affine embeddings (section `Embed`)

Let `ι : GL_m(ℂ) → GL_N(ℂ)` be given on matrices by `Y ↦ L Y + C` with `L` real-linear.

* `contMDiff_comp_affine`: `x ↦ u(c ι(x))` is smooth for smooth `u`. In matrix coordinates it is
  `unitsExtension u ∘ (Y ↦ c (L Y + C))`, which maps units to units.
* `rightDerivative_comp_affine`: if also `L(g Y) = ι(g) L(Y)`, then
  `R(Y)(u(c ι(·)))(g) = (R(L Y) u)(c ι(g))`. The proof uses `rightDerivative_eq_fderiv` and the
  chain rule for the affine map, whose derivative is `W ↦ c L W`.

### Block embeddings (section `Block`)

* `blockDiag_add`, `blockDiag_smul`, `blockDiag_mul`: `diag(A, D)` is additive, real-homogeneous
  and multiplicative.
* `leftLin A = diag(A, 0)` and `rightLin D = diag(0, D)` are continuous real-linear maps.
* `blockDiagGL_left_val`, `blockDiagGL_right_val`: `diag(g, 1) = leftLin g + diag(0, 1)` and
  `diag(1, g) = rightLin g + diag(1, 0)`.
* `leftLin_mul`, `rightLin_mul`: the compatibility `L(g Y) = ι(g) L(Y)`.
* `blockDiagGL_one_one`: `diag(1, 1) = 1`. `blockDiagGL_eq_mul`:
  `diag(g₁, g₂) = diag(g₁, 1) diag(1, g₂)`.
* `blockDiagGL_diagonalUnits_right`, `blockDiagGL_mem_upperUnipotent_right`: the counterparts of
  `ComplexBlockJacquet.blockDiagGL_diagonalUnits` and `blockDiagGL_mem_upperUnipotent` for the
  second block.

### Restriction and slices (section `Restrict`)

* `restrictBlock u (g₁) = u(diag(g₁, 1))` and `sliceFun κ₁ u (g₂) = u(diag(κ₁, g₂))` are linear
  maps.
* `blockDualChar a χ l z = χ_{a+l}(z)⁻¹ (|z|²)^{-a/2}`.
* Smoothness and derivatives: `contMDiff_restrictBlock`, `rightDerivative_restrictBlock`
  (`R(Y) ∘ restrictBlock = restrictBlock ∘ R(diag(Y, 0))`), `contMDiff_sliceFun`,
  `rightDerivative_sliceFun` (`R(Y) ∘ sliceFun κ₁ = sliceFun κ₁ ∘ R(diag(0, Y))`). These come from
  the affine-embedding lemmas, using `sliceFun_eq`: `u(diag(κ₁, g₂)) = u(diag(κ₁, 1) diag(1, g₂))`.
* Translations: `rightTranslation_restrictBlock`, `rightTranslation_sliceFun`, and
  `sliceFun_eq_sliceFun_one`: `sliceFun κ₁ u = sliceFun 1 (R(diag(κ₁, 1)) u)`.
* Characters: `principalSeriesCharacter_addCases_dual` says the character of `χ⁻¹` at
  `(z, 1, …, 1)` is the `GL_a` character of `(blockShiftChar k χ)⁻¹` at `z`.
  `principalSeriesCharacter_addCases_right_dual` says the character of `χ⁻¹` at `(1, …, 1, z)` is
  the `GL_{k+1}` character of `blockDualChar a χ` at `z`. Both follow by comparing exponents
  factor by factor.
* `restrictBlock_mem`: `restrictBlock u` is a `U(a)`-finite function of the principal series of
  `(blockShiftChar k χ)⁻¹`.
* `sliceFun_mem`: `sliceFun κ₁ u` is a `U(k+1)`-finite function of the principal series of `χT`.
  For `U(a+k+1)`-finite `u` of the principal series of `χ⁻¹`, equivariance follows from
  `diag(κ₁, b g₂) = diag(1, b) diag(κ₁, g₂)` and the character lemmas. Finiteness follows because
  the translates of the restricted function are restrictions of translates of `u`.

### Density on the tied block (section `Density`)

* `hyp_principalSeries`: an irreducible complex principal series satisfies
  `GKModuleDensity.Hyp`. Admissibility is the lemma above. Every vector lies in its
  finite-dimensional orbit span (`kFiniteRep_isFiniteVector`,
  `FiniteVectors.orbitSubrepresentation`). Matrix coefficients are continuous
  (`kFiniteRep_continuous`).
* `sliceV κ₁ u` is `sliceFun κ₁ u` as an element of the `U(k+1)`-finite principal series of `χT`.
* `exists_sliceV_eq`: for every element `A` of the free algebra on
  `U(k+1) ⊕ (ℂ ⊗_ℝ 𝔤𝔩_{k+1}(ℂ))` and every `u ∈ U`, some `u' ∈ U` satisfies
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

1. All slices `sliceV κ₁ u` (`κ₁ ∈ U(a)`) lie in the finite-dimensional space `S`. `S` is the
   preimage of the image under `sliceFun 1` of the span of the `U(a+k+1)`-translates of `u`
   (`sliceFun_eq_sliceFun_one`).
2. Take a finite spanning set of `S` (`Submodule.fg_iff_finiteDimensional`) and the rank-one map
   `f(v) = v(1) · φ` (`kFiniteEval`, `LinearMap.smulRight`).
3. `GKModuleDensity.exists_freeAlgebra_eq` gives `A` agreeing with `f` on the spanning set, hence
   on `S` (`LinearMap.eqOn_span`).
4. `exists_sliceV_eq` gives `u' ∈ U` with `u'(diag(κ₁, κ₂)) = u(diag(κ₁, 1)) φ(κ₂)` for unitary
   `κ₁, κ₂`.
5. By orthogonality invariance (`ComplexJacquetDual.integral_mul_eq_zero_of_orthogonal`),
   `∫ u'(κ g) h(κ) dκ = 0` for every `g`.
6. The block limit `ComplexBlockLimit.integral_mul_blockStep_eq_zero` for `u'` gives
   `0 = ∫∫ u'(diag(κ₁, κ₂)) blockStep h (diag(κ₁, κ₂)) = ∫ u(diag(κ₁, 1)) blockPair φ h (κ₁)`.

`map_restrictBlock` holds for nonzero `U` and is not part of the statement. It says that
`U.map restrictBlock` is a nonzero subspace of the `U(a)`-finite principal series of
`(blockShiftChar k χ)⁻¹`, stable under right translation by `U(a)` and under right derivatives.
Nonvanishing follows by translating a `u` with `u(κ) ≠ 0` and evaluating at `1`. This is the input
of the next step of the recursion on `GL_a(ℂ)`.
