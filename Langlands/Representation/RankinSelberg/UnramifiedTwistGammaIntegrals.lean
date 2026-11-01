import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.RankinSelberg.UnramifiedTwistIntegrals
import Langlands.Representation.RankinSelberg.SpectralRescaling

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedGammaTwist

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV uW

section Algebra

variable {F : Type uF} [Field F]

/-- A determinant character trivial on minus one is trivial on every long Weyl element. -/
theorem character_weyl (χ : Fˣ →* ℂˣ) (hχ : χ (-1) = 1) (m : ℕ) :
    χ (determinant (weylLong m F)) = 1 := by
  induction m with
  | zero =>
    have hd : determinant (weylLong 0 F) = 1 := by
      apply Units.ext
      exact Matrix.det_isEmpty
    rw [hd, map_one]
  | succ m hm =>
    rw [RankOneGammaTwist.determinant_weylLong_succ, map_mul, map_pow, hχ, hm]
    simp

/-- The actual block Weyl element also has trivial character. -/
theorem character_blockWeyl (χ : Fˣ →* ℂˣ) (hχ : χ (-1) = 1)
    {n r : ℕ} (hnr : n < r) :
    χ (determinant (blockWeylAt (F := F) n r hnr)) = 1 := by
  have hd : determinant (blockWeylAt (F := F) n r hnr) =
      determinant (weylLong (r - n) F) := by
    apply Units.ext
    change Matrix.det (Matrix.reindex _ _ (blockSum
      ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F)).val) = _
    rw [Matrix.det_reindex_self]
    change Matrix.det (Matrix.reindex _ _ (Matrix.fromBlocks
      (1 : Langlands.GeneralLinear (n + 1) F).val 0 0
      (weylLong (r - n) F).val)) = _
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one,
      Matrix.det_one, one_mul]
    rfl
  rw [hd]
  exact character_weyl χ hχ _

/-- Determinant signs have norm one, so an absolute-value power is trivial on them. -/
theorem character_neg_one (abv : AbsoluteValue F ℝ) (χ : Fˣ →* ℂˣ) (u : ℂ)
    (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u) : χ (-1) = 1 := by
  apply Units.ext
  simp only [hχ, Units.val_neg, Units.val_one, abv.map_neg, map_one, Complex.ofReal_one,
    Complex.one_cpow]

/-- The determinant weight at the inverse determinant has the opposite exponent. -/
theorem product_inverse (abv : AbsoluteValue F ℝ)
    (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
    (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
    (x : Fˣ) :
    (χ₁ x⁻¹ : ℂ) * (χ₂ x⁻¹ : ℂ) = (abv (x : F) : ℂ) ^ (-u) := by
  simp only [map_inv, Units.val_inv_eq_inv_val, ← mul_inv, hprod, Complex.cpow_neg]

end Algebra

section Models

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- Keep the underlying functional on the original carrier. -/
abbrev functional (χ : Fˣ →* ℂˣ) {m : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {θ : upperUnipotent (m + 1) F →* ℂˣ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (L : functionals (upperUnipotent (m + 1) F) θ π) :=
  twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π L

omit [TopologicalSpace F] in
/-- Actual common-vector coefficients multiply by the determinant character. -/
theorem coefficient (χ : Fˣ →* ℂˣ) {m : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {θ : upperUnipotent (m + 1) F →* ℂˣ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (L : functionals (upperUnipotent (m + 1) F) θ π)
    (v : V) (g : Langlands.GeneralLinear (m + 1) F) :
    (modelMap (Langlands.twist (χ.comp determinant) π) (functional χ π L) v).val.val g =
      (χ (determinant g) : ℂ) * (modelMap π L v).val.val g := by
  exact (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
    (determinantCharacter_unipotent χ) π L v) g).symm

omit [TopologicalSpace F] in
/-- Triviality on minus one preserves the model scalar for every model vector. -/
theorem minusOne (χ : Fˣ →* ℂˣ) (hχ : χ (-1) = 1) {m : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {θ : upperUnipotent (m + 1) F →* ℂˣ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (L : functionals (upperUnipotent (m + 1) F) θ π)
    {ζ : ℂˣ} (hζ : HasModelMinusOneScalar π L ζ) :
    HasModelMinusOneScalar (Langlands.twist (χ.comp determinant) π) (functional χ π L) ζ := by
  intro f g
  obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
  rw [coefficient, coefficient, hζ, map_mul, map_mul, Units.val_mul]
  have hd : determinant (-1 : Langlands.GeneralLinear (m + 1) F) = (-1 : Fˣ) ^ (m + 1) := by
    apply Units.ext
    change Matrix.det (-1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = _
    simp [Matrix.det_neg]
  rw [hd, map_pow, hχ]
  simp only [one_pow, Units.val_one, one_mul]
  ring

end Models

section Products

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  {r n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ r π) (L' : glInverseFunctionals ψ n σ) (v : V) (w : W)

include hprod in
/-- Both possible twist positions have the same forward product shift. -/
theorem forward_product (g : Langlands.GeneralLinear (r + 1) F)
    (a : Langlands.GeneralLinear (n + 1) F) (hd : determinant g = determinant a) :
    (modelMap (Langlands.twist (χ₁.comp determinant) π) (functional χ₁ π L) v).val.val g *
      (modelMap (Langlands.twist (χ₂.comp determinant) σ) (functional χ₂ σ L') w).val.val a =
    determinantWeight abv a u * ((modelMap π L v).val.val g * (modelMap σ L' w).val.val a) := by
  rw [coefficient, coefficient, hd]
  change _ = (abv (determinant a : F) : ℂ) ^ u * _
  rw [← hprod]
  ring

variable [IsTopologicalRing F]

include h₁ h₂ hprod in
/-- Inverse transpose gives the negative spectral shift for the actual equal dual. -/
theorem equal_dual_product (hr : r = n) (a : Langlands.GeneralLinear (n + 1) F) :
    (firstDualFunction ψ r
      (modelMap (Langlands.twist (χ₁.comp determinant) π) (functional χ₁ π L) v).val).val
        (hr.symm ▸ a) *
      (secondDualFunction ψ n
        (modelMap (Langlands.twist (χ₂.comp determinant) σ) (functional χ₂ σ L') w).val).val a =
    determinantWeight abv a (-u) *
      ((firstDualFunction ψ r (modelMap π L v).val).val (hr.symm ▸ a) *
        (secondDualFunction ψ n (modelMap σ L' w).val).val a) := by
  subst r
  simp only [firstDualFunction_apply, secondDualFunction_apply, coefficient,
    map_mul, RankOneGammaTwist.determinant_inverseTranspose,
    character_weyl χ₁ h₁, character_weyl χ₂ h₂, one_mul]
  change _ = (abv (determinant a : F) : ℂ) ^ (-u) * _
  rw [← product_inverse abv χ₁ χ₂ u hprod]
  ring

include h₁ h₂ hprod in
/-- The Weyl-translated complementary block has the same negative shift. -/
theorem unequal_dual_product (hnr : n < r)
    (g : Langlands.GeneralLinear (r + 1) F)
    (a : Langlands.GeneralLinear (n + 1) F) (hd : determinant g = determinant a) :
    (translateWhittaker (ψ.scale (-1)) r
      (firstDualFunction ψ r
        (modelMap (Langlands.twist (χ₁.comp determinant) π) (functional χ₁ π L) v).val)
          (blockWeylAt n r hnr)).val g *
      (secondDualFunction ψ n
        (modelMap (Langlands.twist (χ₂.comp determinant) σ) (functional χ₂ σ L') w).val).val a =
    determinantWeight abv a (-u) *
      ((translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r (modelMap π L v).val)
        (blockWeylAt n r hnr)).val g *
        (secondDualFunction ψ n (modelMap σ L' w).val).val a) := by
  simp only [translateWhittaker_apply, firstDualFunction_apply, secondDualFunction_apply,
    coefficient, map_mul, RankOneGammaTwist.determinant_inverseTranspose,
    map_inv, Units.val_inv_eq_inv_val,
    character_weyl χ₁ h₁, character_weyl χ₂ h₂,
    character_blockWeyl χ₁ h₁, inv_one, one_mul, mul_one, hd]
  change _ = (abv (determinant a : F) : ℂ) ^ (-u) * _
  have hp := product_inverse abv χ₁ χ₂ u hprod (determinant a)
  simp only [map_inv, Units.val_inv_eq_inv_val] at hp
  rw [← hp]
  ring

end Products

section ScalarIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- The pointwise equal-rank shift descends through the total integral. -/
theorem equal_integral_shift (μ : Measure (LeftUnipotentQuotient n F))
    (W₁ W₂ : WhittakerFunctions ψ n) (W₁' W₂' : InverseWhittakerFunctions ψ n)
    (u : ℂ)
    (h : ∀ g, W₁.val g * W₁'.val g =
      determinantWeight abv g u * (W₂.val g * W₂'.val g))
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankIntegral ψ abv μ W₁ W₁' Φ =
      fun s => equalRankIntegral ψ abv μ W₂ W₂' Φ (s + u) := by
  funext s
  unfold equalRankIntegral
  rw [equalRankIntegrand_shift_of_product ψ abv u h]

/-- Every rectangular block admits the shift, without an integrability premise. -/
theorem unequal_integral_shift [MeasurableSpace F] (j k : ℕ) (hr : r = n + (j + k + 1))
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W₁ W₂ : WhittakerFunctions ψ r) (W₁' W₂' : InverseWhittakerFunctions ψ n)
    (u : ℂ)
    (h : ∀ g a, determinant g = determinant a →
      W₁.val g * W₁'.val a = determinantWeight abv a u * (W₂.val g * W₂'.val a)) :
    unequalRankIntegralAt j k hr ψ abv μ ν W₁ W₁' =
      fun s => unequalRankIntegralAt j k hr ψ abv μ ν W₂ W₂' (s + u) := by
  subst r
  funext s
  change (∫ q, ∫ x, unequalRankIntegrand ψ abv j k W₁ W₁' s x q ∂ν ∂μ) =
    ∫ q, ∫ x, unequalRankIntegrand ψ abv j k W₂ W₂' (s + u) x q ∂ν ∂μ
  rw [unequalRankIntegrand_shift_of_product ψ abv j k u
    (fun a x => h _ _ (determinant_unequalRankMatrix j k a x))]

end ScalarIntegrals

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  {r n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ r π) (L' : glInverseFunctionals ψ n σ) (v : V) (w : W)

include hprod in
/-- The forward integral shifts by `u` for every unequal-rank decomposition. -/
theorem unequal_forward [MeasurableSpace F] (j k : ℕ) (hr : r = n + (j + k + 1))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)) :
    unequalRankIntegralAt j k hr ψ abv μ ν
      (modelMap (Langlands.twist (χ₁.comp determinant) π) (functional χ₁ π L) v).val
      (modelMap (Langlands.twist (χ₂.comp determinant) σ) (functional χ₂ σ L') w).val =
    fun s => unequalRankIntegralAt j k hr ψ abv μ ν
      (modelMap π L v).val (modelMap σ L' w).val (s + u) := by
  exact unequal_integral_shift ψ abv j k hr μ ν _ _ _ _ u
    (forward_product ψ abv χ₁ χ₂ u hprod π σ L L' v w)

variable [IsTopologicalRing F] [MeasurableSpace F]

include h₁ h₂ hprod in
/-- The actual translated complementary dual integral shifts by `-u`. -/
theorem unequal_dual (hnr : n < r) (j k : ℕ) (hr : r = n + (j + k + 1))
    (ν : AdditiveHaarMeasure F) :
    dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (functional χ₁ π L) (functional χ₂ σ L') (modelMap _ _ v) (modelMap _ _ w) =
    fun s => dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν
      π σ L L' (modelMap _ _ v) (modelMap _ _ w) (s - u) := by
  simpa only [dualUnequalRankModelIntegralAt, sub_eq_add_neg] using
    unequal_integral_shift (ψ.scale (-1)) abv k j (by omega) μ
      (rectangularMeasure ν k (n + 1)) _ _ _ _ (-u)
      (unequal_dual_product ψ abv χ₁ χ₂ u h₁ h₂ hprod π σ L L' v w hnr)

end Integrals

section EqualIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ n π) (L' : glInverseFunctionals ψ n σ) (v : V) (w : W)

include hprod in
/-- Every equal-rank test function is retained in the forward shift. -/
theorem equal_forward (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankModelIntegral ψ abv μ
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (functional χ₁ π L) (functional χ₂ σ L') (modelMap _ _ v) (modelMap _ _ w) Φ =
    fun s => equalRankModelIntegral ψ abv μ π σ L L'
      (modelMap _ _ v) (modelMap _ _ w) Φ (s + u) := by
  exact equal_integral_shift ψ abv μ _ _ _ _ u
    (fun g => forward_product ψ abv χ₁ χ₂ u hprod π σ L L' v w g g rfl) Φ

variable [IsTopologicalRing F]

include h₁ h₂ hprod in
/-- Every Fourier partner is retained in the actual equal-rank dual shift. -/
theorem equal_dual (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    dualEqualRankModelIntegral ψ abv μ
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (functional χ₁ π L) (functional χ₂ σ L') (modelMap _ _ v) (modelMap _ _ w) Φ =
    fun s => dualEqualRankModelIntegral ψ abv μ π σ L L'
      (modelMap _ _ v) (modelMap _ _ w) Φ (s - u) := by
  simpa only [dualEqualRankModelIntegral, sub_eq_add_neg] using
    equal_integral_shift (ψ.scale (-1)) abv μ _ _ _ _ (-u)
      (equal_dual_product ψ abv χ₁ χ₂ u h₁ h₂ hprod π σ L L' v w rfl) Φ

end EqualIntegrals

end Langlands.RankinSelberg.UnramifiedGammaTwist
