# The absolute-domain lower Jacquet functional of the rank-one extension

This module proves
`Langlands.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement.{uF,uW}` from module
`Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement`
(proof task `4dffa0e6-a528-441b-aa62-8cbbbebad5a4`). The theorem is
`Langlands.RankinSelberg.rankOneExtensionLowerJacquetFunctional`; it has no hypotheses.
Worker 234 wrote the proof as a shared draft, and Worker 988 checked and submitted it.

Source: JPSS (1983), proof of Lemma (5.5), printed p. 424, formulas (1) and (3). There,
`λ(σ(g) f)` is the integral of `f(v g)` against `θ̄(v)` wherever that integral converges
absolutely. The Lean proof does not take the stabilized limit (1). It shows that the
integral is a `θ`-equivariant functional on the sections where the integrand at the
identity is integrable. It then extends that functional to the whole representation by
exactness of smooth localization. The statement asks only for this weaker property.

The final theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
The module imports Worker 802's published `RankOneExtensionCellAlgebra` and
`RankOneExtensionLowerCovariance` and redeclares no name from those modules.

## Notation

`n` is an upper unipotent element of `GL_(1+(t+1))(K)`. The published decomposition
`rankOneExtensionUnipotent_decomposition` writes `n = u(β) B(α, 0, 1)`, with
`α = rankOneExtensionUnipotentHead n` (upper unipotent in `GL_(t+1)`) and
`β = rankOneExtensionUnipotentColumn n`. `u(y)` is `rankOneExtensionUpperCell t y`, and
`B(m, x, a)` is `rankOneExtensionLowerBlock t m x a`. `θ_k` is
`Whittaker.inverseStandardCharacter ψ k`. `I(f, g)` is
`rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g`, the function `y ↦ c_f(u(y) g) ψ(y_last)`,
where `c_f` is `rankOneExtensionLowerSectionCoefficient`.

## Section `Algebra`

- `rankOneExtensionUnipotentShift n y := α⁻¹ *ᵥ (y + β)` is the substitution that the change
  of variables uses.
- `rankOneExtensionUpperCell_mul_unipotent`: `u(y) n = B(α, 0, 1) u(α⁻¹ (y + β))`. The proof
  rewrites `B(α,0,1) u(z) = u(α z) B(α,0,1)` (`rankOneExtensionLowerBlock_upperCell`),
  cancels `α α⁻¹`, and uses the decomposition and `u(y) u(β) = u(y + β)`.
- `upperUnipotent_mulVec_last`: an upper unipotent matrix fixes the last coordinate of a
  column vector, because its last row is `(0, …, 0, 1)`.
- `rankOneExtensionUnipotentShift_last`: `(α⁻¹ (y + β))_last = y_last + β_last`. This is the
  previous lemma applied to `α⁻¹`, which is upper unipotent.
- `rankOneExtension_superdiagonal_sum`: the first-superdiagonal sum of `n` equals that of
  `α` plus `β_last`. Both sums are rewritten as sums over `Finset.range` of one function of
  `ℕ`, and `range (t + 1)` is split at `t`.
- `rankOneExtension_inverseStandardCharacter`: `θ_{1+t}(n) = θ_t(α) · ψ(β_last)⁻¹`, by the
  previous lemma and additivity of `ψ`.

## Section `Measure`

The field `K` is a topological ring with its Borel structure and a second-countable
topology.

- `rankOneExtensionShiftMatrix n` is `(α⁻¹)ᵀ`, so that `α⁻¹ *ᵥ x = x ᵥ* (α⁻¹)ᵀ`.
  `det_rankOneExtensionShiftMatrix` shows that its determinant is one: the determinant of
  a transpose is unchanged, and the published `Langlands.RankinSelberg.unipotent_det`
  (upper unipotent matrices have determinant one) applies to `α⁻¹`.
- `rankOneExtensionUnipotentShift_eq`: the substitution is translation by `β` followed by
  the row homeomorphism `rowHomeomorph ((α⁻¹)ᵀ)`.
  `measurableEmbedding_rankOneExtensionUnipotentShift` follows from it.
- `measurePreserving_rankOneExtensionUnipotentShift`: let `ν` be a σ-finite additive Haar
  measure that scales by a character `χ : K →*₀ ℝ≥0` under `x ↦ a x`. Then the
  substitution preserves `rowMeasure ν (t + 1)`. Translation preserves the row product
  measure. The linear part preserves it by `rowMeasure_map_vecMul`, because its
  determinant is one.

## Section `Covariance`

The section first declares two anonymous local instances. They give each factor
`rankOneExtensionLowerCarrier i` of the lower tensor the additive group and complex
module structures of the reversed pair carrier, `Shahidi.pairCarrier … i.rev`. This is
the same pattern as the published `RankOneExtensionLowerCovariance`, so the contraction
lemmas from that module apply.

- `rankOneExtensionTensorContraction_comp_unipotent`: contracting with `ℓ ∘ σ(u)` gives
  `θ_t(u)` times the contraction with `ℓ`. The proof checks pure tensors with
  `piTensorProduct_comp_apply_eq_mul` and `rankOneExtensionTensorContraction_tprod`, then
  applies the `glInverseFunctionals` law of `ℓ`.
- `rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul`:
  `c_f(B(u, 0, 1) g) = θ_t(u) c_f(g)` for upper unipotent `u`. The proof specializes
  `rankOneExtensionLowerSectionCoefficient_lowerBlock_mul` to `x = 0` and `a = 1`. The
  modulus factor is one because `det u = 1`, by the published `unipotent_det` together with
  `Units.ext`.
- `rankOneExtensionStableIntegrand_unipotent_mul`:
  `I(f, n g)(y) = θ_{1+t}(n) · I(f, g)(α⁻¹ (y + β))`. The proof combines the
  factorization, the previous lemma with `u = α`, the character split, the last
  coordinate of the shift and additivity of `ψ`. The factors `ψ(β_last)` cancel because
  `ψ` takes nonzero values.

## Section `Extension`

- `exists_functional_eq_integral_of_covariant` is a generic lemma. Its data are a group
  `G`, a subgroup `U` that is a limit of compact subgroups, a locally constant character
  `θ : U →* ℂˣ`, a smooth representation `ρ` on `V`, a linear map
  `Φ : V →ₗ[ℂ] X → ℂ`, a measure `μ` on `X`, and measure-preserving measurable embeddings
  `s n : X → X` for `n ∈ U`. Assume `Φ(ρ(n) v) = θ(n) · Φ(v) ∘ s n` for all `n` and `v`.
  Then some `L ∈ Whittaker.functionals U θ ρ` satisfies `L v = ∫ Φ v ∂μ` whenever `Φ v` is
  integrable.

  Proof: the vectors with `Φ v` integrable form a `U`-stable submodule `D`, and
  integration is a `θ`-equivariant functional on `D`. Both facts come from the covariance
  and from `MeasurePreserving.integrable_comp_emb` and `MeasurePreserving.integral_comp`.
  `Whittaker.exists_functional_extension_of_subgroup_intertwiner` extends this functional
  from the subrepresentation `D` to `V`.
- `isLocallyConstant_of_continuous_complex_character`: a continuous complex character of
  a nonarchimedean group has an open kernel (`isOpen_ker_of_continuous_complex_character`),
  so it is locally constant.

## Final theorem

`rankOneExtensionLowerJacquetFunctional` introduces the canonical topological data of
`F` and the instances of the statement with tactic `let`. It then applies the generic
lemma with these data:

- `U = upperUnipotent (1 + t + 1)`, which is a limit of compact subgroups by
  `upperUnipotent_isLimitOfCompactSubgroups`;
- `θ = θ_{1+t}`, which is locally constant by the lemma above and
  `Whittaker.inverseStandardCharacterContinuous`;
- `ρ = rankOneExtensionLowerModel F t χ σ`, which is smooth by
  `isSmooth_normalizedOppositeParabolicInduced`;
- `Φ = rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ 1`, `μ = rowMeasure ν (t + 1)`,
  and `s = rankOneExtensionUnipotentShift`.

The scaling hypothesis of the measure lemma comes from `padicScalarHaarScaling`.
`rankOneExtensionStableIntegrand_translate` gives `Φ(I(h) f) = I(f, h)`. With `h = n`,
this turns the integrand covariance into the hypothesis of the generic lemma. With
`h = g`, it turns integrability of `I(f, g)` into integrability of `Φ(I(g) f)`. The
resulting functional then equals `∫ I(f, g)` at `ρ(g) f`.

## Pitfalls

- Do not write `rankOneExtensionLowerInduced F t χlift σ₁` or the lower model explicitly
  as the representation argument. Do not `rw [LinearEquiv.apply_symm_apply]` on its module
  equivalence either. These cause `whnf` timeouts from the `1+(t+1)` versus `(1+t)+1`
  mismatch. Pass `_` and let unification find the representation.
- On terms produced by the generic lemma, `rw` with lemmas about the section type fails
  ("motive is not type correct"). Use `congrArg`, `.trans` and `.mpr` instead.
- Sums over `Fin (1 + t)` do not unify with `Fin (m + 1)` lemmas; go through
  `Fin.sum_univ_eq_sum_range`, as `rankOneExtension_superdiagonal_sum` does.
