# Hermitian Schur orthogonality for coefficient tensors

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.HermitianSchurOrthogonality`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- the published `HarishChandraSchwartz.SchurOrthogonality`: Waldspurger's integrand and integral
  `orthogonalityIntegrand`, `orthogonalityIntegral` (`I(v₁, ℓ₁, v₂, ℓ₂)` of III.1),
  `orthogonalityIntegrand_mk`, `integrable_orthogonalityIntegrand`, III.1 (2)
  `orthogonalityIntegral_eq_zero`, III.1 (3) `formalDegree`, `orthogonalityIntegral_eq_formalDegree`,
  and `isUnitarizable_of_isSquareIntegrable`; through its imports `IsSquareIntegrableModCentralSubgroup`
  (`Representation.Plancherel.CentralSubgroupCoefficients`) and the Hermitian dual
  `InvariantPositiveForm.toSmoothDual`, `InvariantPositiveForm.smoothDualEquiv`
  (`Representation.Unitary.HermitianDual`);
- the published `Representation.Plancherel.CoefficientTensorForm` (Worker 200):
  `coefficientTensorInvariantForm` and `coefficientTensorInvariantForm_inner_tmul`; through it
  `CoefficientTensor P = P ⊗ P̃`, `coefficientTensorMap` with `coefficientTensorMap_tmul`, and
  the transport `coefficientTensorCongr` along an equivalence with `coefficientTensorMap_congr`
  (`CoefficientTensors`), `InvariantPositiveForm.add_right` (`PositiveFormTensor`) and
  `dualInvariantForm` (`SquareIntegrableSemisimplicity`).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proof of Proposition VII.2.1, case `M = G`, printed p. 318 (PDF p. 84): "Des formules
  analogues à III.1 (2) et (3) (pour des produits hermitiens) impliquent que
  `(E^G_G ψ', E^G_G ψ_ω)_{A_G\G} = 0` si `ω' ≄ ω`, `(ψ', ψ_ω)` si `ω' ≃ ω`."
- III.1 (2), (3), printed p. 265 (PDF p. 31): Schur orthogonality and the formal degree, in the
  bilinear form `I(v₁, ℓ₁, v₂, ℓ₂)` formalized in `SchurOrthogonality`.
- VII.1, printed p. 313 (PDF p. 79): `(f₁, f₂)_X = ∫_X conj(f₁(x)) f₂(x) dx`; V.2, printed p. 293
  (PDF p. 59): the product on `L(ω, P)`,
  `(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)`.

Waldspurger states these Hermitian formulas without proof. This module derives them from the
bilinear III.1 (2), (3) for `M = G`. Then `E^G_G` is the coefficient map of `L(ω, G) = E ⊗ Ě`.

### Correspondence with the source

- `G` is a topological group, `A` a normal subgroup contained in the center (in place of
  `A_G`), and `μ` an inversion-invariant Haar measure on `G/A` (in place of the measure on
  `A_G\G`; `A` is central, so `G/A = A\G`).
- `P₁`, `P₂` (in place of `ω`, `ω'`) are smooth complex representations on which `A` acts by the
  same character `χ`. In the source, the formulas are applied to `ω ∈ O` with
  `χ_ω = χ_{ω'}`, after the Fourier inversion over `A_G`.
- `E ψ = coefficientTensorMap P ψ`, so `E(v ⊗ ℓ)(g) = ℓ(P(g) v)`.
- The product on `P ⊗ P̃` is `d⁻¹` times `coefficientTensorInvariantForm P hcof hsq.1 b`, i.e.
  `d⁻¹ b(v₂, v₁) (ℓ₂, ℓ₁)` with `( , )` the form on `P̃` induced by `b`, for any positive
  invariant form `b` on `P` and `d = formalDegree`. This is the product of V.2 for `L(ω, G)`
  (with `M = G`, `I_G^G E = E`), conjugate linear in the first argument as in the source.
- The equivalent case is stated for one representation `P`, and for two representations with
  an equivalence `e : P₁ ≃ P₂`, through the transport `coefficientTensorCongr e : P₁ ⊗ P̃₁ ≃
  P₂ ⊗ P̃₂` (Waldspurger identifies `L(ω', G)` with `L(ω, G)` when `ω' ≃ ω`).

## Scope and hypotheses

Section `Function`: `G` a topological group with `IsTopologicalGroup G`, `A` an arbitrary
subgroup, `χ : A →* ℂˣ`.

- `coefficientTensorMap_mul_of_central A h ψ g a`: `h`, `A` acts on `P` by `χ`.
- `hermitianCoefficientFun ψ₂ ψ₁ g`: no hypotheses.
- `hermitianCoefficientFun_mul`, `hermitianCoefficientIntegrand`,
  `hermitianCoefficientIntegrand_mk`, `_add_left`, `_add_right`: `h₁`, `h₂` (`A` acts on `P₁`
  and on `P₂` by `χ`) and `hu : ∀ a, ‖χ a‖ = 1`.
- `hermitianCoefficientIntegrand_tmul A h₁ h₂ hu b₂ hP₂ v₂ w₂ v₁ ℓ₁`: in addition a positive
  invariant form `b₂` on `P₂` and `hP₂ : IsSmooth P₂.representation`.

Sections `Pairing` and `Equal`: in addition `A` normal with `hA : A ≤ Subgroup.center G`, a
Borel measurable structure on `G/A`, `μ` a Haar measure on `G/A` with `μ.IsInvInvariant`, and
`hcof`: every open subgroup of `G` contains a compact open subgroup.

- `hermitianCoefficientPairing A μ h₁ h₂ hu ψ₂ ψ₁`: no further hypotheses.
- `integrable_hermitianCoefficientIntegrand A hA μ hcof h₁ h₂ hu hsq₁ hsq₂ b₂ ψ₂ ψ₁`: `hsq₁`,
  `hsq₂` (`P₁`, `P₂` square integrable modulo `A` for `μ`, which includes admissibility) and a
  positive invariant form `b₂` on `P₂`.
- `hermitianCoefficientPairing_eq_zero A hA μ hcof h₁ h₂ hu hsq₁ hsq₂ hi₁ hi₂ hne ψ₂ ψ₁`: `hsq₁`,
  `hsq₂`, `hi₁`, `hi₂` (irreducibility) and `hne : IsEmpty (P₁.representation.Equiv
  P₂.representation)` (inequivalence).
- `hermitianCoefficientPairing_eq_inner A hA μ hcof h hu hsq hi b ψ₂ ψ₁`: one representation `P`
  with `h`, `hu`, `hsq`, `hi` and a positive invariant form `b` on `P`.

Section `Equivalent`: the setting of `Pairing`.

- `hermitianCoefficientIntegrand_congr A h₁ h₂ hu e ψ₂ ψ₁`: an equivalence
  `e : P₁.representation.Equiv P₂.representation` (no measure-theoretic hypotheses are used).
- `hermitianCoefficientPairing_eq_inner_of_equiv A hA μ hcof h₁ h₂ hu e hsq₂ hi₂ b₂ ψ₂ ψ₁`: `e`,
  `hsq₂`, `hi₂` and a positive invariant form `b₂` on `P₂`.

## Definitions

- `hermitianCoefficientFun ψ₂ ψ₁ g = conj((E ψ₂)(g)) (E ψ₁)(g)` on `G`.
- `hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ : G ⧸ A → ℂ`, its descent to `G/A`
  (`Quotient.lift`), well defined by `hermitianCoefficientFun_mul`.
- `hermitianCoefficientPairing A μ h₁ h₂ hu ψ₂ ψ₁ = ∫_{G/A} conj((E ψ₂)(g)) (E ψ₁)(g) dμ`,
  Waldspurger's `(E ψ₂, E ψ₁)_{A_G\G}`.

## Results

- `coefficientTensorMap_mul_of_central`: `(E ψ)(g a) = χ(a) (E ψ)(g)` for `a ∈ A`.
- `hermitianCoefficientFun_mul`: the integrand is right `A`-invariant (because `|χ| = 1`).
- `hermitianCoefficientIntegrand_add_left`, `_add_right`: additivity in each tensor.
- `hermitianCoefficientIntegrand_tmul`: for `ψ₂ = v₂ ⊗ b₂(w₂, -)` and `ψ₁ = v₁ ⊗ ℓ₁` the
  integrand is `orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ w₂ b₂(v₂, -)`, the integrand of
  `I(v₁, ℓ₁, w₂, b₂(v₂, -))`.
- `integrable_hermitianCoefficientIntegrand`: the integrand is `μ`-integrable.
- `hermitianCoefficientPairing_eq_zero` (**Hermitian III.1 (2)**): `(E ψ₂, E ψ₁)_{G/A} = 0` for
  inequivalent irreducible `P₁`, `P₂`.
- `hermitianCoefficientPairing_eq_inner` (**Hermitian III.1 (3)**):
  `(E ψ₂, E ψ₁)_{G/A} = d⁻¹ (ψ₂, ψ₁)` for one irreducible `P`, with `d = formalDegree` and the
  tensor form `(v₂ ⊗ ℓ₂, v₁ ⊗ ℓ₁) = b(v₂, v₁)(ℓ₂, ℓ₁)` of `coefficientTensorInvariantForm`.
- `hermitianCoefficientIntegrand_congr`: replacing `ψ₁` by `e_* ψ₁ = coefficientTensorCongr e ψ₁`
  does not change the integrand.
- `hermitianCoefficientPairing_eq_inner_of_equiv`: for `e : P₁ ≃ P₂`,
  `(E ψ₂, E ψ₁)_{G/A} = d(P₂)⁻¹ (ψ₂, e_* ψ₁)` with the tensor form on `P₂ ⊗ P̃₂`.

## Proof notes

1. On pure tensors `E(v ⊗ ℓ)(g a) = ℓ(P(g)(χ(a) v)) = χ(a) E(v ⊗ ℓ)(g)`; the general case is
   additive (`TensorProduct.inductionOn`). Then `conj(χ(a) x) χ(a) y = |χ(a)|² conj(x) y`.
2. Every smooth functional on `P₂` is `b₂(w₂, -)` (`smoothDualEquiv`, which uses `hcof` and
   admissibility). For `ψ₂ = v₂ ⊗ b₂(w₂, -)`,
   `conj(b₂(w₂, P₂(g) v₂)) = b₂(P₂(g) v₂, w₂) = b₂(v₂, P₂(g⁻¹) w₂)` by Hermitian symmetry and
   invariance of `b₂`, so the integrand is `ℓ₁(P₁(g) v₁) b₂(v₂, P₂(g⁻¹) w₂)`, Waldspurger's
   integrand of `I(v₁, ℓ₁, w₂, b₂(v₂, -))`.
3. Integrability, vanishing and the formula reduce to pure tensors by induction on both tensors
   (integrability of the summands gives `integral_add'`). On pure tensors they are
   `integrable_orthogonalityIntegrand`, `orthogonalityIntegral_eq_zero` and
   `orthogonalityIntegral_eq_formalDegree`. In the vanishing theorem the form `b₂` comes from
   `isUnitarizable_of_isSquareIntegrable`.
4. In the equal case, writing also `ℓ₁ = b(w₁, -)`, III.1 (3) gives
   `d⁻¹ b(v₂, v₁) b(w₁, w₂)`. The tensor form gives `b(v₂, v₁)` times the dual form
   `(b(w₂, -), b(w₁, -)) = b(w₁, w₂)` (`dualInvariantForm`, by definition through the inverse of
   `smoothDualEquiv`).

5. For an equivalence `e`, `coefficientTensorMap_congr` gives `E(e_* ψ₁) = E ψ₁`, so the
   integrand is the one for `P₂` alone, and step 4 applies to `P₂`.

## Relation to the Library

`SchurOrthogonality` proves III.1 (2), (3) for the bilinear integral `I(v₁, ℓ₁, v₂, ℓ₂)` and
`TraceOrthogonality` their trace forms. `FourierTransform` proves Lemma VII.1.1 (ii),
`∫ conj(E ψ) f = (ψ, f̂)`, with the same tensor form. No other Library declaration states the
orthogonality of coefficients in the Hermitian form used in the proof of Proposition VII.2.1.

## Open obligations

The identification of `d` and of the tensor form with Waldspurger's `d(ω)` and product on
`L(ω, G)` for his measures, and the remaining steps of Proposition VII.2.1.
