import Langlands.Representation.RankinSelberg.UnequalRankDualCharacterChange
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeAlgebra

/-!
# Fixed-functional transport of the unequal-rank epsilon equation

For `ψ^a(x) = ψ(ax)`, the translated functionals `v ↦ ℓ(π(D) v)`,
`u ↦ ℓ'(σ(d_a) u)` and an additive Haar measure `ν' = κ ν` with `κ² = |a|`,
every original and every dual unequal-rank integral for `ψ^a` is a fixed
nonzero monomial in `q^(-s)` times the corresponding integral for `ψ` of the
vectors `π(R) v` and `u`. The fixed-monomial functional equation for `ψ` then
gives the one for `ψ^a`, with the coefficient multiplied by
`ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` and the exponent shifted by
`N ord a`, `N = (r+1)(n+1)`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped NNReal

universe uF uV uW

section Transfer

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The fixed-monomial epsilon equation transfers to new functionals, character
and Haar measure when, block by block, the new original and dual integrals are
fixed nonzero monomials times the old ones of `T v` and `u`, with `T`
surjective, and the minus-one scalar of the second model is preserved. -/
theorem UnequalRankEpsilonEquation.transfer {hnr : n < r} {q : ℕ} (hq : 0 < q)
    {ψ ψ₂ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)} {ν ν₂ : AdditiveHaarMeasure F}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    {ℓ₂ : glFunctionals ψ₂ r π} {ℓ₂' : glInverseFunctionals ψ₂ n σ}
    {c c' : ℂˣ} {m m' : ℤ}
    (h : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m)
    (hζ : ∀ ζ, HasModelMinusOneScalar σ ℓ' ζ → HasModelMinusOneScalar σ ℓ₂' ζ)
    {T : V → V} (hT : Function.Surjective T)
    (hblock : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)), ∃ (α β : ℂˣ) (A B : ℤ),
      m' + A = m - B ∧ (c' : ℂ) * α = c * β * (q : ℂ) ^ (-B) ∧
      (∀ v u s, unequalRankIntegralAt j k hr ψ₂ abv μ (rectangularMeasure ν₂ j (n + 1))
          (modelMap π ℓ₂ v).val (modelMap σ ℓ₂' u).val s =
        α * spectralPoint q s ^ A * unequalRankIntegralAt j k hr ψ abv μ
          (rectangularMeasure ν j (n + 1)) (modelMap π ℓ (T v)).val (modelMap σ ℓ' u).val s) ∧
      (∀ v u s, dualUnequalRankModelIntegralAt hnr j k hr ψ₂ abv μ ν₂ π σ ℓ₂ ℓ₂'
          (modelMap π ℓ₂ v) (modelMap σ ℓ₂' u) s =
        β * spectralPoint q s ^ B * dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ
          ℓ ℓ' (modelMap π ℓ (T v)) (modelMap σ ℓ' u) s)) :
    UnequalRankEpsilonEquation hnr q ψ₂ abv μ ν₂ π σ ℓ₂ ℓ₂' c' m' := by
  obtain ⟨ζ, P, Pdual, hζ₀, hall⟩ := h
  refine ⟨ζ, P, Pdual, hζ ζ hζ₀, fun j k hr => ?_⟩
  obtain ⟨α, β, A, B, hm, hc, hI, hD⟩ := hblock j k hr
  obtain ⟨hP, hPd, hFE⟩ := hall j k hr
  have hS := zetaSpan_values_eq_of_monomial
    (I₁ := fun (x : (coefficientModel π ℓ).toSubmodule)
      (y : (coefficientModel σ ℓ').toSubmodule) =>
        unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) x.val y.val)
    (I₂ := fun (x : (coefficientModel π ℓ₂).toSubmodule)
      (y : (coefficientModel σ ℓ₂').toSubmodule) =>
        unequalRankIntegralAt j k hr ψ₂ abv μ (rectangularMeasure ν₂ j (n + 1)) x.val y.val)
    hq (modelMap_surjective π ℓ) (modelMap_surjective σ ℓ') (modelMap_surjective π ℓ₂)
    (modelMap_surjective σ ℓ₂') hT α A hI
  have hSd := zetaSpan_values_eq_of_monomial
    (I₁ := dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ')
    (I₂ := dualUnequalRankModelIntegralAt hnr j k hr ψ₂ abv μ ν₂ π σ ℓ₂ ℓ₂')
    hq (modelMap_surjective π ℓ) (modelMap_surjective σ ℓ') (modelMap_surjective π ℓ₂)
    (modelMap_surjective σ ℓ₂') hT β B hD
  refine ⟨?_, ?_, ?_⟩
  · rw [unequalRankValuesAt_eq] at hP ⊢
    exact ⟨hP.1, hS ▸ hP.2⟩
  · exact ⟨hPd.1, hSd ▸ hPd.2⟩
  · exact functionalEquation_transfer_of_monomial
      (I₁ := fun (x : (coefficientModel π ℓ).toSubmodule)
        (y : (coefficientModel σ ℓ').toSubmodule) =>
          unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) x.val y.val)
      (I₂ := fun (x : (coefficientModel π ℓ₂).toSubmodule)
        (y : (coefficientModel σ ℓ₂').toSubmodule) =>
          unequalRankIntegralAt j k hr ψ₂ abv μ (rectangularMeasure ν₂ j (n + 1)) x.val y.val)
      (D₁ := dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ')
      (D₂ := dualUnequalRankModelIntegralAt hnr j k hr ψ₂ abv μ ν₂ π σ ℓ₂ ℓ₂')
      hq (modelMap_surjective π ℓ₂) (modelMap_surjective σ ℓ₂') α β A B hI hD hm hc hFE

end Transfer

section MinusOne

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The translated second functional has the same minus-one scalar. -/
theorem HasModelMinusOneScalar.characterChange {ψ : UnitaryAdditiveCharacter F} (a : Fˣ)
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ' : glInverseFunctionals ψ n σ} {ζ : ℂˣ} (h : HasModelMinusOneScalar σ ℓ' ζ) :
    HasModelMinusOneScalar σ (characterChangeInverseFunctional ψ σ a ℓ') ζ := by
  intro f g
  obtain ⟨u, rfl⟩ := modelMap_surjective σ (characterChangeInverseFunctional ψ σ a ℓ') f
  rw [modelMap_characterChangeInverseFunctional, characterChangeInverseFunction_apply,
    characterChangeInverseFunction_apply,
    show characterChangeElement a n * ((-1) * g) = (-1) * (characterChangeElement a n * g) by
      rw [neg_one_mul, neg_one_mul, mul_neg]]
  exact h (modelMap σ ℓ' u) (characterChangeElement a n * g)

end MinusOne

section Blocks

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (a : Fˣ)
  (μ : Measure (LeftUnipotentQuotient n F))
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
  {ν ν₂ : AdditiveHaarMeasure F} [SigmaFinite ν.measure] (κ : ℝ≥0)
  (hκ : ν₂.measure = κ • ν.measure)
  (hμ : HasCharacterChangeMeasureLaw abv a μ)
  (e : ℤ) (he : abv (Matrix.det (characterChangeElement a n).val) = (q : ℝ) ^ (-e))

include hq hκ hμ he in
/-- The original integral of block `(j, k)` for the translated functionals,
`ψ^a` and `ν₂ = κ ν` is a monomial times the one for `ψ` of `π(R) v` and `u`. -/
theorem forwardBlock_characterChange {j k : ℕ} (hr : r = n + (j + k + 1))
    [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (hρ : HasCharacterChangeRectangularMeasureLaw abv a j n (rectangularMeasure ν j (n + 1)))
    (v : V) (u : W) (s : ℂ) :
    unequalRankIntegralAt j k hr (ψ.scale a) abv μ (rectangularMeasure ν₂ j (n + 1))
        (modelMap π (characterChangeFunctional ψ π a ℓ) v).val
        (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u).val s =
      ((((κ ^ (j * (n + 1)) : ℝ≥0) : ℝ) : ℂ) *
          (unequalRankCharacterChangeScalar abv a n j k : ℂ)) * spectralPoint q s ^ (-e) *
        unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
          (modelMap π ℓ (π (blockCorrectionAt a n r) v)).val (modelMap σ ℓ' u).val s := by
  rw [modelMap_characterChangeFunctional, modelMap_characterChangeInverseFunctional,
    unequalRankIntegralAt_congr_smul abv j k μ hr rfl (κ ^ (j * (n + 1)))
      (rectangularMeasure_eq_smul κ hκ j (n + 1)) 1 1 (fun _ => (one_mul _).symm)
      (fun _ => (one_mul _).symm) s,
    unequalRankIntegralAt_characterChange q hq ψ abv a j k μ _ hμ hρ e he hr]
  ring

variable (ωπ ωσ : Fˣ →* ℂˣ)

include hq hκ hμ he in
/-- The dual integral of block `(j, k)` for the translated functionals,
`ψ^a` and `ν₂ = κ ν` is a monomial times the one for `ψ` of `π(R) v` and `u`;
the central characters enter through the scalar matrices. -/
theorem dualBlock_characterChange (hnr : n < r)
    (hπ : Classification.HasGLCentralCharacter F (r + 1) π ωπ)
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ)
    (hμr : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    {j k : ℕ} (hr : r = n + (j + k + 1)) [BorelSpace (Matrix (Fin k) (Fin (n + 1)) F)]
    (hρ : HasCharacterChangeRectangularMeasureLaw abv a k n (rectangularMeasure ν k (n + 1)))
    (hρg : ∀ (g : Langlands.GeneralLinear (n + 1) F)
      (G : Matrix (Fin k) (Fin (n + 1)) F → ℂ),
      ∫ x, G (x * g.val) ∂(rectangularMeasure ν k (n + 1)) =
        determinantWeight abv g (-(k : ℂ)) * ∫ x, G x ∂(rectangularMeasure ν k (n + 1)))
    (v : V) (u : W) (s : ℂ) :
    dualUnequalRankModelIntegralAt hnr j k hr (ψ.scale a) abv μ ν₂ π σ
        (characterChangeFunctional ψ π a ℓ) (characterChangeInverseFunctional ψ σ a ℓ')
        (modelMap π (characterChangeFunctional ψ π a ℓ) v)
        (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u) s =
      ((((κ ^ (k * (n + 1)) : ℝ≥0) : ℝ) : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) *
          ((ωσ a : ℂˣ) : ℂ) ^ n * (unequalRankCharacterChangeScalar abv a n k j : ℂ) *
          ((ωσ (a ^ (r - n + 1)) : ℂˣ) : ℂ)) *
        (spectralPoint q s ^ (-e) *
          determinantWeight abv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1)))
            (((k + j + 1 : ℕ) : ℂ) / 2 - s - k)) *
        dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ'
          (modelMap π ℓ (π (blockCorrectionAt a n r) v)) (modelMap σ ℓ' u) s := by
  have hr' : r = n + (k + j + 1) := by omega
  set b : Fˣ := (a ^ (r - n + 1))⁻¹ with hb
  set g : Langlands.GeneralLinear (n + 1) F := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b
  have hψ : (ψ.scale (-1)).scale a = (ψ.scale a).scale (-1) := by
    rw [UnitaryAdditiveCharacter.scale_scale, UnitaryAdditiveCharacter.scale_scale, mul_comm]
  have hιg : inverseTranspose (n + 1) F g =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1)) := by
    rw [inverseTranspose_scalar', hb, inv_inv]
  have hg : g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1)) := by
    rw [← map_inv, hb, inv_inv]
  -- the first-stage identity: central characters and the rectangular scaling
  have h1 := unequalRankIntegralAt_congr_smul abv k j μ hr' hψ (κ ^ (k * (n + 1)))
    (rectangularMeasure_eq_smul κ hκ k (n + 1))
    (W₂ := translateWhittaker ((ψ.scale a).scale (-1)) r
      (firstDualFunction (ψ.scale a) r (modelMap π (characterChangeFunctional ψ π a ℓ) v).val)
      (blockWeylAt n r hnr))
    (W₂' := secondDualFunction (ψ.scale a) n
      (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u).val)
    _ _ (firstDual_modelMap_characterChangeFunctional ψ a π ℓ ωπ hπ hnr v)
    (secondDual_modelMap_characterChangeInverseFunctional ψ a σ ℓ' ωσ hσ u) s
  -- the forward change of character for `ψ^(-1)` in block `(k, j)`
  have h2 := unequalRankIntegralAt_characterChange q hq (ψ.scale (-1)) abv a k j μ _ hμ hρ e he
    hr'
  -- the translation law for the scalar `diag(b I, I)`
  have h3 := dualIntegralAt_translate' ψ abv μ hnr hr' hμr g
    (ρ := rectangularMeasure ν k (n + 1)) (fun G => hρg _ G)
    (W₁ := (modelMap π ℓ (π (blockCorrectionAt a n r) v)).val)
    (W₂ := (modelMap π ℓ (π (GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega))
      (appendIdentity n (r - n) g)) (π (blockCorrectionAt a n r) v))).val)
    (W₁' := (modelMap σ ℓ' (σ g⁻¹ u)).val) (W₂' := (modelMap σ ℓ' u).val)
    (fun h => by
      change ℓ.val (π h (π _ (π (blockCorrectionAt a n r) v))) =
        ℓ.val (π (h * _) (π (blockCorrectionAt a n r) v))
      rw [map_mul, Module.End.mul_apply])
    (fun h => by
      change ℓ'.val (σ h u) = ℓ'.val (σ (h * g) (σ g⁻¹ u))
      rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (σ g), ← map_mul,
        mul_inv_cancel, map_one, Module.End.one_apply]) s
  -- the central character of `σ` on the second dual vector
  have h4 := unequalRankIntegralAt_congr_smul abv k j μ hr' rfl 1 (one_smul _ _).symm
    (W₁ := translateWhittaker (ψ.scale (-1)) r
      (firstDualFunction ψ r (modelMap π ℓ (π (blockCorrectionAt a n r) v)).val)
      (blockWeylAt n r hnr))
    (W₂ := translateWhittaker (ψ.scale (-1)) r
      (firstDualFunction ψ r (modelMap π ℓ (π (blockCorrectionAt a n r) v)).val)
      (blockWeylAt n r hnr))
    (W₁' := secondDualFunction ψ n (modelMap σ ℓ' u).val)
    (W₂' := secondDualFunction ψ n (modelMap σ ℓ' (σ g⁻¹ u)).val)
    (ρ₁ := rectangularMeasure ν k (n + 1)) 1 ((ωσ (a ^ (r - n + 1)) : ℂˣ) : ℂ)
    (fun _ => (one_mul _).symm)
    (fun h => by
      rw [secondDualFunction_apply, secondDualFunction_apply]
      change ℓ'.val (σ _ (σ g⁻¹ u)) = _ * ℓ'.val (σ _ u)
      rw [hg, hσ, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul]) s
  rw [hιg] at h3
  unfold dualUnequalRankModelIntegralAt
  rw [h1, h2]
  erw [h3, h4]
  simp only [NNReal.coe_one, Complex.ofReal_one, one_mul]
  ring

end Blocks

section Constants

/-- A positive real base raised to a complex power, in exponential form. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp (Real.log x * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

/-- A natural power of a positive real, in exponential form. -/
theorem ofReal_pow_eq_exp {x : ℝ} (hx : 0 < x) (m : ℕ) :
    ((x ^ m : ℝ) : ℂ) = Complex.exp (Real.log x * m) := by
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ofReal_cpow_eq_exp hx]

/-- `2 ∑_{i ≤ n} (n - i) = n (n + 1)`. -/
theorem sum_fin_sub_mul_two (n : ℕ) : (∑ i : Fin (n + 1), (n - i.val)) * 2 = n * (n + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => n - i) (n + 1)]
  have h := Finset.sum_range_reflect (fun i => i) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, Finset.sum_range_id_mul_two, Nat.add_sub_cancel, mul_comm]

/-- `2 ∑_{i < j} (i + 1) = j (j + 1)`. -/
theorem sum_fin_succ_mul_two (j : ℕ) : (∑ i : Fin j, (i.val + 1)) * 2 = j * (j + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1) j]
  have h := Finset.sum_range_succ' (fun i => i) j
  simp only [add_zero] at h
  rw [← h, Finset.sum_range_id_mul_two, Nat.add_sub_cancel, mul_comm]

variable {F : Type uF} [Field F]

/-- The absolute determinant of `d_a = diag(a^n, ..., a, 1)`. -/
theorem abv_det_characterChangeElement (abv : AbsoluteValue F ℝ) (a : Fˣ) (n : ℕ) :
    abv (Matrix.det (characterChangeElement a n).val) =
      abv (a : F) ^ (∑ i : Fin (n + 1), (n - i.val)) := by
  rw [characterChangeElement_val, Matrix.det_diagonal, map_prod, ← Finset.prod_pow_eq_pow_sum]
  simp only [Units.val_pow_eq_pow_val, map_pow]

/-- The absolute determinant of a scalar matrix. -/
theorem abv_det_scalar (abv : AbsoluteValue F ℝ) (m : ℕ) (b : Fˣ) :
    abv (Matrix.det (Matrix.GeneralLinearGroup.scalar (Fin m) b).val) = abv (b : F) ^ m := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

/-- The exponent of `|det d_a|` in terms of the exponent of `|a|`. -/
theorem abv_det_characterChangeElement_eq_zpow (q : ℕ) (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (o : ℤ) (ho : abv (a : F) = (q : ℝ) ^ (-o)) (n : ℕ) :
    abv (Matrix.det (characterChangeElement a n).val) =
      (q : ℝ) ^ (-(o * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℤ))) := by
  rw [abv_det_characterChangeElement, ho, ← zpow_natCast, ← zpow_mul, neg_mul]

/-- The exponent of `|det(b I)|`, `b = a^t`, in terms of the exponent of `|a|`. -/
theorem abv_det_scalar_pow_eq_zpow (q : ℕ) (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (o : ℤ) (ho : abv (a : F) = (q : ℝ) ^ (-o)) (m t : ℕ) :
    abv (Matrix.det (Matrix.GeneralLinearGroup.scalar (Fin m) (a ^ t)).val) =
      (q : ℝ) ^ (-(o * ((t * m : ℕ) : ℤ))) := by
  rw [abv_det_scalar, Units.val_pow_eq_pow_val, map_pow, ho, ← pow_mul, ← zpow_natCast,
    ← zpow_mul, neg_mul]

/-- Splitting off the spectral part of a determinant weight. -/
theorem determinantWeight_sub_eq (q : ℕ) (hq : 0 < q) (abv : AbsoluteValue F ℝ) {m : ℕ}
    (g : Langlands.GeneralLinear m F) (e : ℤ) (h : abv (Matrix.det g.val) = (q : ℝ) ^ (-e))
    (t s : ℂ) :
    determinantWeight abv g (t - s) = determinantWeight abv g t * spectralPoint q s ^ (-e) := by
  have hd : ((abv (Matrix.det g.val) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abv.ne_zero g.det_ne_zero)
  rw [show determinantWeight abv g (t - s) =
      determinantWeight abv g t / determinantWeight abv g s from Complex.cpow_sub t s hd,
    determinantWeight_eq_spectralPoint_zpow q hq abv g e h s, zpow_neg, div_eq_mul_inv]

/-- The block constants match. With `|a| = q^(-o)`, `κ² = |a|` and `r = n + (j + k + 1)`,
the new coefficient times the original-side constant of block `(j, k)` equals the old
coefficient times the dual-side constant and the change of spectral exponent. -/
theorem blockConstants_eq (q : ℕ) (hq : 0 < q) (abv : AbsoluteValue F ℝ) (a : Fˣ) (o : ℤ)
    (ho : abv (a : F) = (q : ℝ) ^ (-o)) (κ : ℝ≥0) (hκ2 : (κ : ℝ) ^ 2 = abv (a : F))
    {n r j k : ℕ} (hr : r = n + (j + k + 1)) (c wπ wσ : ℂ) :
    c * wπ ^ (n + 1) * wσ ^ (r + 1) *
        ((abv (a : F) : ℝ) : ℂ) ^ (-(((r + 1) * (n + 1) : ℕ) : ℂ) / 2) *
        ((((κ ^ (j * (n + 1)) : ℝ≥0) : ℝ) : ℂ) *
          (unequalRankCharacterChangeScalar abv a n j k : ℂ)) =
      c * (((((κ ^ (k * (n + 1)) : ℝ≥0) : ℝ) : ℂ) * wπ ^ (n + 1) * wσ ^ n *
          (unequalRankCharacterChangeScalar abv a n k j : ℂ) * wσ ^ (r - n + 1)) *
          determinantWeight abv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1)))
            (((k + j + 1 : ℕ) : ℂ) / 2 - k)) *
        (q : ℂ) ^ (-(-(o * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℤ)) -
          o * (((r - n + 1) * (n + 1) : ℕ) : ℤ))) := by
  subst hr
  have hA : 0 < abv (a : F) := abv.pos (Units.ne_zero a)
  have hκ : 0 < (κ : ℝ) := by
    rcases (κ.coe_nonneg).lt_or_eq with h | h
    · exact h
    · rw [← h] at hκ2; simp at hκ2; exact absurd hκ2.symm hA.ne'
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hla : Real.log (abv (a : F)) = -(o : ℝ) * Real.log q := by
    rw [ho, Real.log_zpow, Int.cast_neg]
  have hlk : Real.log κ = Real.log (abv (a : F)) / 2 := by
    rw [← hκ2, Real.log_pow]; push_cast; ring
  have hS := sum_fin_sub_mul_two n
  have hJ := sum_fin_succ_mul_two j
  have hK := sum_fin_succ_mul_two k
  have hd : n + (j + k + 1) - n + 1 = j + k + 2 := by omega
  rw [hd]
  -- exponential forms
  have e1 : ((abv (a : F) : ℝ) : ℂ) ^ (-(((n + (j + k + 1) + 1) * (n + 1) : ℕ) : ℂ) / 2) =
      Complex.exp (Real.log (abv (a : F)) * (-(((n + (j + k + 1) + 1) * (n + 1) : ℕ) : ℂ) / 2)) :=
    ofReal_cpow_eq_exp hA _
  have eκ : ∀ m : ℕ, (((κ ^ m : ℝ≥0) : ℝ) : ℂ) = Complex.exp (Real.log κ * m) := fun m => by
    rw [NNReal.coe_pow, ofReal_pow_eq_exp hκ]
  have eU : ∀ j k : ℕ, (unequalRankCharacterChangeScalar abv a n j k : ℂ) =
      Complex.exp (Real.log (abv (a : F)) * (characterChangeRootExponent n : ℂ)) *
        Complex.exp (Real.log (abv (a : F)) * (((n + 1) * ∑ i : Fin j, (i.val + 1) : ℕ) : ℂ)) /
        Complex.exp (Real.log (abv (a : F)) * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℂ) *
          (-((j + k + 1 : ℕ) : ℂ) / 2)) := fun j k => by
    rw [unequalRankCharacterChangeScalar_val, determinantWeight, abv_det_characterChangeElement,
      ofReal_cpow_eq_exp (pow_pos hA _), Real.log_pow]
    rw [show ((characterChangeModulus abv a n : ℝ) : ℂ) =
        ((abv (a : F) ^ characterChangeRootExponent n : ℝ) : ℂ) from rfl,
      show ((characterChangeRectangularModulus abv a j n : ℝ) : ℂ) =
        ((abv (a : F) ^ ((n + 1) * ∑ i : Fin j, (i.val + 1)) : ℝ) : ℂ) from rfl,
      ofReal_pow_eq_exp hA, ofReal_pow_eq_exp hA]
    push_cast
    ring_nf
  have eW : determinantWeight abv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (j + k + 2)))
      (((k + j + 1 : ℕ) : ℂ) / 2 - k) =
      Complex.exp (Real.log (abv (a : F)) * (((j + k + 2) * (n + 1) : ℕ) : ℂ) *
        (((k + j + 1 : ℕ) : ℂ) / 2 - k)) := by
    rw [determinantWeight, abv_det_scalar, Units.val_pow_eq_pow_val, map_pow, ← pow_mul,
      ofReal_cpow_eq_exp (pow_pos hA _), Real.log_pow]
    push_cast
    ring_nf
  have eq : ∀ B : ℤ, (q : ℂ) ^ B = Complex.exp (Real.log q * B) := fun B => by
    rw [← Complex.cpow_intCast, ← Complex.ofReal_natCast, ofReal_cpow_eq_exp hq']
  rw [e1, eκ, eκ, eU, eU, eW, eq]
  -- compare the exponents
  have key : Complex.exp (Real.log (abv (a : F)) *
        (-(((n + (j + k + 1) + 1) * (n + 1) : ℕ) : ℂ) / 2)) *
      (Complex.exp (Real.log κ * ((j * (n + 1) : ℕ) : ℂ)) *
        (Complex.exp (Real.log (abv (a : F)) * (characterChangeRootExponent n : ℂ)) *
          Complex.exp (Real.log (abv (a : F)) * (((n + 1) * ∑ i : Fin j, (i.val + 1) : ℕ) : ℂ)) /
          Complex.exp (Real.log (abv (a : F)) * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℂ) *
            (-((j + k + 1 : ℕ) : ℂ) / 2)))) =
      Complex.exp (Real.log κ * ((k * (n + 1) : ℕ) : ℂ)) *
        (Complex.exp (Real.log (abv (a : F)) * (characterChangeRootExponent n : ℂ)) *
          Complex.exp (Real.log (abv (a : F)) * (((n + 1) * ∑ i : Fin k, (i.val + 1) : ℕ) : ℂ)) /
          Complex.exp (Real.log (abv (a : F)) * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℂ) *
            (-((k + j + 1 : ℕ) : ℂ) / 2))) *
        Complex.exp (Real.log (abv (a : F)) * (((j + k + 2) * (n + 1) : ℕ) : ℂ) *
          (((k + j + 1 : ℕ) : ℂ) / 2 - k)) *
        Complex.exp (Real.log q * ((-(-(o * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℤ)) -
          o * (((j + k + 2) * (n + 1) : ℕ) : ℤ)) : ℤ) : ℂ)) := by
    simp only [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    generalize (∑ i : Fin (n + 1), (n - i.val)) = S at hS ⊢
    generalize (∑ i : Fin j, (i.val + 1)) = J at hJ ⊢
    generalize (∑ i : Fin k, (i.val + 1)) = K at hK ⊢
    have hS' : (S : ℂ) * 2 = n * (n + 1) := by exact_mod_cast hS
    have hJ' : (J : ℂ) * 2 = j * (j + 1) := by exact_mod_cast hJ
    have hK' : (K : ℂ) * 2 = k * (k + 1) := by exact_mod_cast hK
    have hla' : (Real.log (abv (a : F)) : ℂ) = -(o : ℂ) * Complex.log q := by
      rw [hla]; push_cast; ring
    have hlk' : (Real.log κ : ℂ) = Real.log (abv (a : F)) / 2 := by
      rw [hlk]; push_cast; ring
    push_cast
    rw [hlk', hla']
    linear_combination (-(o : ℂ) * Complex.log q * (n + 1) / 2) * (hJ' - hK') +
      (-(o : ℂ) * Complex.log q / 2) * hS'
  linear_combination (c * wπ ^ (n + 1) * wσ ^ (n + (j + k + 1) + 1)) * key

end Constants

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The fixed-monomial unequal-rank epsilon equation for `ψ`, `ν` and `(ℓ, ℓ')`
gives the one for `ψ^a`, `ν₂ = κ ν` with `κ² = |a|` and the translated
functionals, with the coefficient multiplied by
`ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` and the exponent shifted by `N o`, where
`|a| = q^(-o)` and `N = (r+1)(n+1)`. The measure laws are hypotheses. -/
theorem UnequalRankEpsilonEquation.characterChange
    [∀ t : ℕ, BorelSpace (Matrix (Fin t) (Fin (n + 1)) F)]
    (hnr : n < r) (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (a : Fˣ) (o : ℤ) (ho : abv (a : F) = (q : ℝ) ^ (-o))
    (μ : Measure (LeftUnipotentQuotient n F)) (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (hμr : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (ν ν₂ : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (κ : ℝ≥0)
    (hκ : ν₂.measure = κ • ν.measure) (hκ2 : (κ : ℝ) ^ 2 = abv (a : F))
    (hρ : ∀ t : ℕ, HasCharacterChangeRectangularMeasureLaw abv a t n
      (rectangularMeasure ν t (n + 1)))
    (hρg : ∀ (t : ℕ) (g : Langlands.GeneralLinear (n + 1) F)
      (G : Matrix (Fin t) (Fin (n + 1)) F → ℂ),
      ∫ x, G (x * g.val) ∂(rectangularMeasure ν t (n + 1)) =
        determinantWeight abv g (-(t : ℂ)) * ∫ x, G x ∂(rectangularMeasure ν t (n + 1)))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (ωπ ωσ : Fˣ →* ℂˣ)
    (hπ : Classification.HasGLCentralCharacter F (r + 1) π ωπ)
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ)
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ} {c : ℂˣ} {m : ℤ}
    (h : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m) (c' : ℂˣ)
    (hc' : (c' : ℂ) = c * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
      ((abv (a : F) : ℝ) : ℂ) ^ (-(((r + 1) * (n + 1) : ℕ) : ℂ) / 2)) :
    UnequalRankEpsilonEquation hnr q (ψ.scale a) abv μ ν₂ π σ
      (characterChangeFunctional ψ π a ℓ) (characterChangeInverseFunctional ψ σ a ℓ') c'
      (m + ((r + 1) * (n + 1) : ℕ) * o) := by
  have hA : 0 < abv (a : F) := abv.pos (Units.ne_zero a)
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [NNReal.coe_zero, zero_pow two_ne_zero] at hκ2
    exact hA.ne' hκ2.symm
  have hκm : ∀ t : ℕ, ((((κ ^ t : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (pow_ne_zero _ hκ0))
  have he := abv_det_characterChangeElement_eq_zpow q abv a o ho n
  have hT : Function.Surjective (π (blockCorrectionAt a n r)) := fun v =>
    ⟨π (blockCorrectionAt a n r)⁻¹ v, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  refine h.transfer hq (fun ζ hζ => hζ.characterChange a) hT (fun j k hr => ?_)
  refine ⟨Units.mk0 ((((κ ^ (j * (n + 1)) : ℝ≥0) : ℝ) : ℂ) *
      (unequalRankCharacterChangeScalar abv a n j k : ℂ)) (mul_ne_zero (hκm _) (Units.ne_zero _)),
    Units.mk0 (((((κ ^ (k * (n + 1)) : ℝ≥0) : ℝ) : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) *
        ((ωσ a : ℂˣ) : ℂ) ^ n * (unequalRankCharacterChangeScalar abv a n k j : ℂ) *
        ((ωσ (a ^ (r - n + 1)) : ℂˣ) : ℂ)) *
      determinantWeight abv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1)))
        (((k + j + 1 : ℕ) : ℂ) / 2 - k))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hκm _)
        (pow_ne_zero _ (Units.ne_zero _))) (pow_ne_zero _ (Units.ne_zero _)))
        (Units.ne_zero _)) (Units.ne_zero _)) (determinantWeight_ne_zero abv _ _)),
    -(o * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℤ)),
    -(o * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℤ)) - o * (((r - n + 1) * (n + 1) : ℕ) : ℤ),
    ?_, ?_, ?_, ?_⟩
  · -- the exponents
    have hS := sum_fin_sub_mul_two n
    have hd : r - n + 1 = j + k + 2 := by omega
    have hr' : (r : ℤ) = n + (j + k + 1) := by exact_mod_cast hr
    rw [hd]
    generalize (∑ i : Fin (n + 1), (n - i.val)) = S at hS ⊢
    have hS' : (S : ℤ) * 2 = n * (n + 1) := by exact_mod_cast hS
    push_cast
    linear_combination (-o) * hS' + ((n : ℤ) + 1) * o * hr'
  · -- the coefficients
    rw [Units.val_mk0, Units.val_mk0, hc', map_pow, Units.val_pow_eq_pow_val]
    exact blockConstants_eq q hq abv a o ho κ hκ2 hr _ _ _
  · -- the original integrals
    intro v u s
    rw [Units.val_mk0]
    exact forwardBlock_characterChange q hq ψ abv a μ π σ ℓ ℓ' κ hκ hμ _ he hr (hρ j) v u s
  · -- the dual integrals
    intro v u s
    rw [dualBlock_characterChange q hq ψ abv a μ π σ ℓ ℓ' κ hκ hμ _ he ωπ ωσ hnr hπ hσ hμr hr
        (hρ k) (hρg k) v u s, sub_right_comm _ s,
      determinantWeight_sub_eq q hq abv _ _
        (abv_det_scalar_pow_eq_zpow q abv a o ho (n + 1) (r - n + 1)),
      Units.val_mk0, Int.sub_eq_add_neg, zpow_add₀ (spectralPoint_ne_zero_of_pos hq s)]
    ring

end Generic

end Langlands.RankinSelberg
