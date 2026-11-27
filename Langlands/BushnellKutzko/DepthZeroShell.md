# The extreme determinant shell at depth zero

## Setting

`K` is a `p`-adic field (`PadicField p`) with its canonical topology, valuation and local-field
structure, ring of integers `𝔬_K = 𝒪[K.Carrier]`, a uniformizer `ϖ` (`Irreducible ϖ`) and residue
field `k = IsLocalRing.ResidueField 𝔬_K`, which is finite. `ψ` is a Library
`UnitaryAdditiveCharacter K.Carrier` of conductor `𝔬_K` (`Conductor.HasIntegerConductor ψ`), `ν`
a σ-finite `AdditiveHaarMeasure K.Carrier`, and `GL_{n+1}(K)` carries its Borel structure and the
Haar measure `RankinSelberg.generalLinearHaar K.Carrier n`, which gives
`K₀ = GL_{n+1}(𝔬_K)` (`Conductor.integralSubgroup`) mass one. `𝓢 = LatticeChain.standard hϖ` is
the standard lattice chain, whose `d`-th filtration step `𝔓^d` consists of the matrices with
entries in `ϖ^d 𝔬_K`.

## Main result

`standardDepthZeroShellNonzero_of_finiteMatrixGaussInjectivity`:
`FiniteMatrixGaussInjectivityStatement → StandardDepthZeroShellNonzero`. Spelled out: let `σ`
be a smooth representation of `GL_{n+1}(K)` and `w ≠ 0` a vector fixed by the first unit group
`U¹(𝓢) = 1 + ϖ M_{n+1}(𝔬_K)`. Let `Φ = stratumTest K 𝓢 le_rfl ψ 0` be the indicator of `U¹(𝓢)`.
Then some smooth functional `ℓ` satisfies

`∫_{ord(det g) = -(n+1)} Φ̂(g) ℓ(σ(g^{-T}) w) dg ≠ 0`,

with `Φ̂ = rectangularFourierIntegral ψ ν Φ`. This is the form of the integral in
`StandardDepthZeroShellNonzero` (module `Langlands.BushnellKutzko.SupercuspidalConductorDepthZeroReduction`),
whose integrand is `Φ̂(g) · coefficientIota (stratumCoefficient K σ ℓ w) g`.

## Other declarations

*Reduction modulo the maximal ideal* (for a local ring `R`, a group `G` and a homomorphism
`ι : GL_n(R) → G`):

- `IntegralMatrices.map_residue_surjective`: `GL_n(R) → GL_n(R/𝔪)` is surjective.
- `generalLinear_map_inverseTranspose`: change of coefficients commutes with `g ↦ g^{-T}`.
- `addChar_eq_of_residue_eq`, `residueCharacter`, `residueCharacter_residue`: an additive
  character of `R` trivial on `𝔪` descends to the residue field.
- `reductionKernelFixedVectors ι σ`: the vectors fixed by `σ(ι(k))` for all `k ≡ 1 mod 𝔪`.
- `reductionKernelAction ι σ`: the action `k ↦ σ(ι(k^{-T}))` of `GL_n(R)` on these vectors.
- `reductionRepresentation ι σ`: the induced representation of `GL_n(R/𝔪)`, with
  `reductionRepresentation_map`: `ρ(k̄) v = σ(ι(k^{-T})) v`.

*The standard chain*: `toLin'_mem_standard_endFiltration` and
`entry_mem_of_toLin'_mem_standard_endFiltration` identify `𝔓^d(𝓢)` with the matrices whose
entries lie in `ϖ^d 𝔬_K`.

*Integration over `GL_{n+1}(𝔬_K)`*:

- `integralInclusion K n : GL_{n+1}(𝔬_K) → GL_{n+1}(K)` and
  `integralInclusion_mem_unitSubgroup_one`: an integral matrix `≡ 1 mod 𝔭_K` lies in `U¹(𝓢)`.
- `setIntegral_preimage_mul_left`, `setIntegral_subgroup_mul_left`: translation identities for a
  left-invariant measure.
- `isOpen_integralSubgroup_padic`, `isCompact_integralSubgroup_padic`.
- `setIntegral_integralSubgroup_eq_average`: if `F` is continuous and
  `F(ι(k)) = Θ(k mod 𝔭_K)` for all `k ∈ GL_{n+1}(𝔬_K)`, then
  `∫_{K₀} F = |GL_{n+1}(k)|⁻¹ ∑_{ḡ} Θ(ḡ)`.

*The scalar matrix `ϖ · 1`* (`uniformizerScalar`): its entrywise action
(`uniformizerScalar_mul_apply`, `uniformizerScalar_inv_mul_apply`),
`inverseTranspose_uniformizerScalar_inv : ((ϖ · 1)⁻¹)^{-T} = ϖ · 1`, the determinant
(`det_uniformizerScalar_mul`, `ord_uniformizerScalar_mul`),
`ord_det_eq_of_uniformizerScalar_mul_mem` (if `ϖ g ∈ K₀` then `ord(det g) = -(n+1)`) and
`uniformizerScalar_mul_mem_of_entries` (if the entries of `ϖ g` are integral and
`ord(det g) = -(n+1)`, then `ϖ g ∈ K₀`).

*The character and the Fourier transform*:

- `residueScaledCharacter`: `x̄ ↦ ψ(ϖ⁻¹ x)` on `k`; `residueScaledCharacter_residue` and
  `residueScaledCharacter_ne_one` (it is nontrivial since `ψ` has conductor `𝔬_K`).
- `measurableSet_standard_matrixFiltration_one`: `𝔓 = ϖ M_{n+1}(𝔬_K)` is measurable.
- `uniformizerScalar_mul_mem_of_fourier_ne_zero`: on the shell `ord(det g) = -(n+1)`, `Φ̂(g) ≠ 0`
  forces `ϖ g ∈ K₀`.
- `rectangularFourierIntegral_stratumTest_of_mem`: if `ϖ g ∈ K₀`, then
  `Φ̂(g) = vol(𝔓) ψ(tr g)`, the volume taken for `RankinSelberg.rectangularMeasure ν`.
- `standard_matrixFiltration_one_volume_ne_zero`: `vol(𝔓) ≠ 0`.
- `trace_uniformizerScalar_inv_mul`, `trace_integralInclusion`, `trace_map_residue`: traces of
  `ϖ⁻¹ g`, of an integral matrix in `K`, and of its reduction.

## Provenance

The calculation is the depth-zero case of Bushnell–Fröhlich (1985), (3.3.10)–(3.3.15), printed
pp. 259–260: the Fourier transform of the indicator of `1 + ϖ M_N(𝔬)` is a nonzero constant times
`ψ(tr y)` on `ϖ⁻¹ M_N(𝔬)`, and the shell `ord(det) = -N` of the reflected zeta integral is a
nonzero multiple of the finite Gauss operator, composed with the action of `ϖ⁻¹ I_N`. The
paired Markdown of `FiniteMatrixGaussInjectivityStatement` describes the same reduction. The
representation of `GL_{n+1}(k)` here acts through the inverse transpose, because the shell
integral involves `σ(g^{-T})`.

## Proof

*Fourier transform.* By the Library bound `toLin'_inv_smul_transpose_mem_of_fourier_ne_zero`
(with `t = ϖ⁻¹`, filtration index `0`), `Φ̂(g) ≠ 0` implies that `ϖ gᵀ` has integral entries;
with `ord(det g) = -(n+1)` this gives `ϖ g ∈ K₀`. If `ϖ g ∈ K₀` and `y ∈ 𝔓`, then
`tr(y gᵀ) = ∑ (ϖ⁻¹ y_{ab})(ϖ g_{ab}) ∈ 𝔬_K`, so `ψ(tr(y gᵀ)) = 1`, and
`rectangularFourierIntegral_twistedIndicator_of_trace_eq_one` (module `FourierSupport`) gives
`Φ̂(g) = vol(𝔓) ψ(tr g)`. The set `𝔓` is open, compact and nonempty, so its volume for the
product Haar measure is positive and finite.

*Averaging.* For `F` continuous, each translate `x ↦ F(s(ḡ) x)` by a chosen lift
`s(ḡ) ∈ K₀` of `ḡ ∈ GL_{n+1}(k)` is integrable on the compact set `K₀` and has the same integral
over `K₀` as `F`, by left invariance. Summing over `ḡ`, at `x = ι(k)` the sum of the translates
is `∑_{ḡ} Θ(ḡ · k̄) = ∑_ḡ Θ(ḡ)`, and `K₀` has mass one.

*The residue representation.* Since `ρ'(k) = σ(ι(k^{-T}))` is trivial on the kernel of reduction,
it factors through `GL_{n+1}(k)` (`MonoidHom.liftOfSurjective`).

*The main theorem.* By `integralInclusion_mem_unitSubgroup_one`, `w` lies in the
reduction-kernel fixed vectors. Gauss injectivity, applied over the finite field `k` to the
nontrivial character `ψ̄ = residueScaledCharacter` and the representation
`ρ = reductionRepresentation`, gives `T w ≠ 0` for `T = ∑_ḡ ψ̄(tr ḡ) ρ(ḡ)`. Then
`u = σ(ϖ · 1)(T w) ≠ 0`, and `exists_smoothDual_apply_ne_zero_of_compact_cofinal` with
`GeneralLinear.compactOpen_cofinal` gives a smooth functional `ℓ` with `ℓ(u) ≠ 0`.

For this `ℓ`, write `I(g) = Φ̂(g) ℓ(σ(g^{-T}) w)`. The set `{g | ϖ g ∈ K₀}` lies in the shell, and
`I` vanishes on the rest of the shell, so the shell integral is `∫_{ϖ g ∈ K₀} I`
(`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`), which equals `∫_{K₀} I(ϖ⁻¹ k) dk` by
`setIntegral_preimage_mul_left`. For `k ∈ K₀`,
`I(ϖ⁻¹ k) = vol(𝔓) ψ(tr(ϖ⁻¹ k)) ℓ(σ(ϖ · 1) σ(k^{-T}) w)` because `(ϖ⁻¹ k)^{-T} = (ϖ · 1) k^{-T}`.
This is a continuous function `F` of `k` (the coefficient is locally constant,
`GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients`). At `k = ι(k')` it equals
`Θ(k̄') = vol(𝔓) ψ̄(tr k̄') ℓ(σ(ϖ · 1) ρ(k̄') w)`. The averaging lemma and linearity of `ℓ` give

`∫_{ord(det g) = -(n+1)} I = |GL_{n+1}(k)|⁻¹ vol(𝔓) ℓ(u)`,

a product of nonzero factors.
