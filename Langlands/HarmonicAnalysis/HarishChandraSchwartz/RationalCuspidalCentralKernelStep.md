# The local kernel step of Waldspurger VIII.4.1

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, proof of Proposition VIII.4.1, printed pp. 328–330 (PDF pp. 94–96),
registered source `waldspurger-2003-plancherel`.

This module is the local kernel step of the proof of VIII.4.1. It proves the
finite dimensionality of the actual central level span from an explicit
function `E` with the properties of Waldspurger's `°e`. The proof goes through
the Library's abstract kernel theorem `finiteDimensional_of_kernelAlphaChi`
(`KernelQuotient`). It does not construct `°e`, and it does not prove the
closed target `RationalCuspidalCentralProjectionFiniteStatement`.

## The source step

Let `e` be the characteristic function of a compact open subgroup `H`. When
`χ` is trivial on `A_G ∩ H`, the source uses the cuspidal projection `°e` of
VIII.2. It records that `°e ∈ °C_H`, that `°e` is real, and that `°e` is
supported in `G¹`. Lemma VIII.2.3 gives `φ * °e = φ * e = mes(H) φ` for
`φ ∈ °C_H`. With `α(g₁, g₂) = mes(H)⁻² ∫_H °e(g₁⁻¹ h g₂) dh` and
`α_χ(·, g₂) = p_χ α(·, g₂)`, the source asserts `α(·, g₂) ∈ °C_H`. It then
proves the reproducing formula (1) and concludes with the diagonal integral,
which VIII.3.2 makes finite.

## The interface: `IsRationalCuspidalLevelKernel`

`IsRationalCuspidalLevelKernel hKc hPK ρ muG H E` is a Prop-valued
structure. Here `E` is an element of the actual rational Schwartz space
`RationalSchwartzSpace hKc hPK ρ`, `H : OpenSubgroup (rationalPoints G)` and
`muG` is a measure on `G(F)`. The fields are:

- `mem_level`: `E ∈ rationalCuspidalLevel hKc hPK ρ H` (the source's
  `°e ∈ °C_H`);
- `conj_eq`: `conj (E x) = E x` for all `x` (`°e` is real);
- `inv_eq`: `E x⁻¹ = E x` for all `x`. The source does not list this
  property explicitly, but it uses it when it asserts `α(·, g₂) ∈ °C_H`. It
  follows from the commutation of the projection with `f ↦ f^∨` (Remark
  VIII.2.2), since `e^∨ = e`;
- `eq_zero_of_not_mem`: `E x = 0` for `x ∉ G¹ = rationalCommonNormKernel G`
  (`°e` is supported in `G¹`);
- `convolution_eq`: for every `φ ∈ rationalCuspidalLevel hKc hPK ρ H` and
  every `x`, `convolution muG φ E x = (muG H).toReal * φ x`, where
  `convolution μ f₁ f₂ g = ∫ h, f₁ h * f₂ (h⁻¹ * g) ∂μ`. This is Lemma VIII.2.3,
  `φ * °e = mes(H) φ`. `E` is the projection of the unnormalized
  characteristic function of `H`.

The field `eq_zero_of_not_mem` is not used in this module. It is the input that
reduces the diagonal prerequisite below to VIII.3.2, as in the source.

`levelMeasure muG H` is the restriction `muG.comap H.subtype` of `muG` to `H`.
It is the measure `dh` in `α`. `levelMeasure_univ` shows
`levelMeasure muG H univ = muG H`. `levelMeasure_isMulLeftInvariant` shows that
it is left invariant when `muG` is. For a Haar measure `muG` and compact `H`,
`levelMeasure_univ_toReal_ne_zero` shows that its total mass is a nonzero
real, and `levelMeasure_isFiniteMeasure` shows that it is finite.

## The named open prerequisite: the diagonal

`RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E` states the
following. Take any right-invariance instance for `muA`, any Borel measurable
structure on `A_G(F) \ G(F)` (`LeftQuotient`), and any quotient measure `muQ`
compatible with `muG` and `muA` (`IsCompatible`). Then the function
`q ↦ Re α_χ(q̇, q̇)` is `muQ`-integrable, where `q̇ = q.out` and
`α_χ = kernelAlphaChi muA χ (levelMeasure muG H) E`. This is the source's
convergence of `∫_{A_G\G} α_χ(g, g) dg`. The source derives it from
`°e ∈ °C_H`, the support of `°e` in `G¹` and VIII.3.2. Here it is an explicit
hypothesis.

## The main theorem

`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan` assumes:

- `hs : IsSplitComponent s`, a Haar measure `muA` on the literal point image
  `A_G(F) = (rationalPoints.map s).range`, and a unitary character `χ`;
- a Haar measure `muG` on `G(F)` with `[muG.IsMulRightInvariant]`
  (unimodularity of `G(F)`);
- a compact open `H` and `E` with `IsRationalCuspidalLevelKernel hKc hPK ρ muG H E`;
- the weight structures `CentralWeights muA Ξ σ`, `L2Weights muG Ξ σ` and
  `ConvolutionWeights muG K' Ξ σ` for some compact subgroup `K'`, where
  `Ξ = rationalXi hKc hPK` and `σ = rationalHeight ρ`;
- `RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E`.

It concludes
`FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H)`.
No hypothesis on `χ` restricted to `A_G ∩ H` is needed.

`rationalHaar_isMulRightInvariant` proves that every Haar measure on `G(F)`
is right invariant for connected reductive `G`. The modular character is
trivial (`rationalPoints_modularCharacter_eq_one`), and Mathlib's
`Measure.map_right_mul_eq_modularCharacterFun_smul` gives
`map (· * g) μ = Δ(g) μ`.
`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_connectedReductive`
is the main theorem with the hypothesis `IsConnectedReductive G` in place of
`[muG.IsMulRightInvariant]`.

### Proof

The proof applies `finiteDimensional_schwartzCentralIntegralSpan_of_kernel`
(below) with `W = rationalCuspidalLevel hKc hPK ρ H` and
`μ_H = levelMeasure muG H`. It supplies its inputs as follows.

- `A_G(F)` is closed (`isClosed_range_splitComponent`) and central
  (`IsCentral.range_le_center`). It is therefore locally compact and second
  countable, and `muA` is regular. `isMulRightInvariant_of_le_center` and
  `isInvInvariant_of_le_center` give right invariance and inversion
  invariance of `muA`.
- A compatible quotient measure `muQ` on `A_G(F) \ G(F)`, with its Borel
  structure, exists by `QuotientIntegration.compatibleMeasureExists`. This
  is the only use of `[muG.IsMulRightInvariant]`.
- Convergence of the central integrals: `CentralWeights.convergesOn`.
- Left `H`-invariance of `φ ∈ W`: bi-invariance.
- Reproduction: `convolution_eq` together with `levelMeasure_univ`.
- Triple integrability: `integrable_kernelTriple`.
- Kernel translates: `exists_mem_eq_integral_kernel` applied to
  `S = rationalCuspidalSubmodule`, which is stable under translations
  (`translate_mem_rationalCuspidalSubmodule`, with
  `rationalTranslationWeights`). This gives `ψ ∈ S` with
  `ψ(g) = ∫_H E(g⁻¹ h y) dh`. Then `mes(H)⁻² ψ` lies in `S`. It is
  `H`-bi-invariant by `isBiInvariant_integral_kernel`, so it lies in `W`. Its
  central integral is `α_χ(·, y)` by definition of `kernelAlphaChi`.
- Quotient products: `integrable_centralProjection_mul_conj_out` (central
  weights and `L²` weights).
- Diagonal: the prerequisite at `muQ`.

## Generic results

- `finiteDimensional_schwartzCentralIntegralSpan_of_kernel` (generic form).
  Let `W` be a submodule of a Schwartz space `Space Ξ σ` on a locally
  compact, second countable, Hausdorff group. Let `A` be a closed central
  subgroup, `ν` a compatible quotient measure, `χ` unitary and `E` real, with
  `mes(H) ≠ 0`. Assume the following: the central integrals converge on `W`;
  every `φ ∈ W` is left `H`-invariant, satisfies `φ * E = mes(H) φ` and has
  integrable triple integrands; every `α_χ(·, y)` is `p_χ ψ` for some
  `ψ ∈ W`; the quotient products are integrable; and the diagonal is
  integrable. Then `schwartzCentralIntegralSpan W μA χ` is finite
  dimensional. The proof identifies the span with the raw image
  (`coe_schwartzCentralIntegralSpan_eq_image`), checks `IsKernelAlphaChiSpace`
  and the hypotheses of `finiteDimensional_of_kernelAlphaChi`, and applies
  that theorem.
- `integrable_kernelTriple`. Let `E` and `φ` be continuous with all `ν_r`
  finite, `φ` left `H`-invariant, `μ_G` left invariant and `μ_H` finite.
  Assume `ConvolutionWeights μ_G K Ξ σ` and `CentralWeights μ_A Ξ σ`. Then
  `(g', a, h) ↦ E(g'⁻¹ h a g) φ(g')` is integrable on `G × A × H`. The proof
  bounds the lower Lebesgue integral. By Tonelli
  (`lintegral_prod_symm`), the inner integral over `G` comes first. The
  substitution `g' ↦ h g'` (`lintegral_mul_left_eq_self`) and left
  invariance of `φ` remove `h`. Lemma III.6.1's estimate
  (`ConvolutionWeights.lintegral_enorm_mul_le`) bounds the inner integral
  by `C (1 + σ(a))^{-s}`, using `Ξ(a g) = Ξ(g)` and
  `CentralWeights.rpow_neg_le`. Here `s` comes from
  `CentralWeights.exists_lintegral_lt_top`, and `C` involves
  `ν_{s+d}(φ) ν_s(E)` and the finite integral of `Ξ² (1 + σ)^{-d}`.
- `integral_apply_eq_sum_of_isLocallyConstant`. For a locally constant
  family `F : X → Y → ℂ` on a compact space with a finite measure,
  `∫ F x w dμ = Σ_{c ∈ range F} μ(F⁻¹{c}) c(w)`. The range is finite
  (`IsLocallyConstant.range_finite`) and the fibres are open.
- `isLocallyConstant_kernelIntegrand`. If `H` is open and `E` is right
  `H`-invariant, then `h ↦ (g ↦ E(g⁻¹ h y))` is locally constant on `H`.
  Indeed it is unchanged when `h` is replaced by `h k` with `y⁻¹ k y ∈ H`.
- `isBiInvariant_integral_kernel`. If `E` is `H`-bi-invariant and `μ_H` is
  left invariant, then `g ↦ ∫_H E(g⁻¹ h y) dμ_H` is `H`-bi-invariant.
- The existing `IsIntegrableUnipotentCuspidal.translate` from `SchwartzCompactLifting`. Two-sided translates preserve
  the cusp condition `∀ x y, ∫_U f(x u y) du = 0` (with integrability).
- `exists_mem_eq_integral_kernel`. Let `S` be a submodule of the Schwartz
  space stable under the left translations `Space.translate hTW 1 g`. Let
  `E ∈ S` satisfy `E(x⁻¹) = E(x)` and be right invariant under the open
  compact `H`. Then `g ↦ ∫_H E(g⁻¹ h y) dμ_H` is an element of `S`. By the
  two previous lemmas it equals `Σ_c μ_H(F⁻¹{c}) E(y⁻¹ h_c⁻¹ g)`, a finite
  combination of left translates of `E`.
- `Space.continuous_and_nu_lt_top`: elements of a Schwartz space are
  continuous with all `ν_r` finite.
- `mul_comm_of_le_center`, `isMulRightInvariant_of_le_center` and
  `isInvInvariant_of_le_center`. A central subgroup is commutative. A
  left-invariant measure on it is right invariant. A regular Haar measure on
  it is inversion invariant: the proof uses Mathlib's
  `IsHaarMeasure.isInvInvariant_of_regular` for a local `CommGroup` structure.

## Open hypotheses

The main theorem leaves the hypotheses below open. None of them is same-rank
finiteness, same-rank reconstruction, the closed target or a dimension bound.

- `IsRationalCuspidalLevelKernel hKc hPK ρ muG H E` for `E = °e`, the actual
  degree-zero projection of the characteristic function of `H`. The rank
  adapter (`IsRationalCuspidalUnit`, module `RationalCuspidalUnit`) gives the same five
  properties from six laws of a linear projection. The laws, including the
  translation law, concern the actual degree-zero projection of VIII.2, which
  is not in the Library; its construction needs strictly-smaller-rank inputs
  from a mutual induction over rank.
- `CentralWeights muA Ξ σ`: from `RationalSplitCenterHeightStatement`
  (`RationalSplitCenterHeightStatement.centralWeights`), proved as
  `rationalSplitCenterHeight` (module `RationalSplitCenterHeightProof`).
- `L2Weights muG Ξ σ` and `ConvolutionWeights muG K' Ξ σ`: from Lemma II.1.5,
  `RationalXiSquareIntegrableStatement`, through the Library adapters
  `RationalXiSquareIntegrableStatement.l2Weights` and `.convolutionWeights`.
  The Library proves II.1.5 only from `RationalXiUpperBoundStatement`, the
  upper bound of Lemma II.1.1 (`rationalXiSquareIntegrable_of_upperBound`).
  That upper bound is proved as `rationalXiUpperBound` (module `RationalXiUpperBoundProof`).
  The adapters also take structural premises: a compact open `K0` with
  `SimultaneousStandardBasisAt i ν K0` and `FiniteCartanCovering F i ν K0`,
  and, for the convolution weights, `K' ≤ rationalHeightSubgroup ρ`.
  Supplying them for every structural choice belongs to the closed assembly
  of the target.
- `RationalLevelKernelDiagonalIntegrable`: from VIII.3.2. Its statement
  `RationalCuspidalConjugationIntegrabilityStatement` (module
  `RationalCuspidalConjugationStatement`) is in the Library and is not proved
  there. The reduction of this prerequisite to that statement's integrability
  form is carried out in the modules
  `RationalCuspidalCentralKernelDiagonal` and
  `RationalCuspidalCentralKernelPairing`.

The instance `[muG.IsMulRightInvariant]` of the main theorem (unimodularity of
`G(F)`) is not open for connected reductive `G`.
`rationalHaar_isMulRightInvariant` derives it from the Library's
`rationalPoints_modularCharacter_eq_one`. That lemma applies
`rationalReductiveUnimodularity` with the proved `standardCocharacter`, which
discharges its `StandardCocharacterStatement` premise.
`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_connectedReductive`
states the kernel step without this instance.
