import Langlands.Representation.RankinSelberg.PairGammaTwistExchangeStatement
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-!
# Determinant twists in the JPSS integrals of a pair

For a representation `π` of `GL_(r+1)`, a representation `σ` of `GL_(n+1)` with `n ≤ r` and a
character `χ`, this module compares the JPSS integrals of the pairs `(π ⊗ χ ∘ det, σ)` and
`(π, σ ⊗ χ ∘ det)`, with the same underlying Whittaker functionals: the forward integrals
agree, the dual integrals differ by the sign `χ(-1)^((n+1)(r-n))`, and the minus-one scalar of
the test model changes by `χ(-1)^(n+1)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.PairGammaTwistExchange

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV uW

section Determinants

variable {F : Type uF} [Field F]

theorem determinant_weylLong_zero : determinant (weylLong 0 F) = 1 := by
  apply Units.ext
  change Matrix.det (weylLong 0 F).val = 1
  exact Matrix.det_isEmpty

/-- Block expansion of the determinant of the long Weyl matrix. -/
theorem determinant_weylLong_add (a b : ℕ) :
    determinant (weylLong (a + b) F) =
      (-1 : Fˣ) ^ (a * b) * (determinant (weylLong a F) * determinant (weylLong b F)) := by
  induction b with
  | zero => simp [determinant_weylLong_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, RankOneGammaTwist.determinant_weylLong_succ, ih,
      RankOneGammaTwist.determinant_weylLong_succ, Nat.mul_succ]
    simp only [pow_add]
    ac_rfl

/-- The determinant of `diag(I_(n+1), w_(r-n))`. -/
theorem determinant_blockWeyl (n r : ℕ) (hnr : n < r) :
    determinant (blockWeylAt (F := F) n r hnr) = determinant (weylLong (r - n) F) := by
  apply Units.ext
  change Matrix.det (Matrix.reindex _ _ (blockSum ((1 : Langlands.GeneralLinear (n + 1) F),
    weylLong (r - n) F)).val) = _
  rw [Matrix.det_reindex_self]
  change Matrix.det (Matrix.reindex _ _ (Matrix.fromBlocks
    (1 : Langlands.GeneralLinear (n + 1) F).val 0 0 (weylLong (r - n) F).val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one,
    Matrix.det_one, one_mul]
  rfl

/-- The long Weyl element of rank `r + 1` against the two Weyl factors of the dual test. -/
theorem determinant_weyl_ratio (n r : ℕ) (hnr : n < r) :
    determinant (weylLong (r + 1) F) =
      (-1 : Fˣ) ^ ((n + 1) * (r - n)) *
        (determinant (weylLong (n + 1) F) * determinant (blockWeylAt (F := F) n r hnr)) := by
  rw [determinant_blockWeyl]
  have key : ∀ m : ℕ, m = (n + 1) + (r - n) →
      determinant (weylLong m F) = (-1 : Fˣ) ^ ((n + 1) * (r - n)) *
        (determinant (weylLong (n + 1) F) * determinant (weylLong (r - n) F)) := by
    rintro m rfl
    exact determinant_weylLong_add (n + 1) (r - n)
  exact key (r + 1) (by omega)

/-- The determinants of the two dual arguments differ by `(-1)^((n+1)(r-n))`. -/
theorem determinant_dual_arguments (n r : ℕ) (hnr : n < r)
    (g : Langlands.GeneralLinear (r + 1) F) (a : Langlands.GeneralLinear (n + 1) F)
    (hdet : determinant g = determinant a) :
    determinant (weylLong (r + 1) F * inverseTranspose (r + 1) F (g * blockWeylAt n r hnr)) =
      (-1 : Fˣ) ^ ((n + 1) * (r - n)) *
        determinant (weylLong (n + 1) F * inverseTranspose (n + 1) F a) := by
  rw [map_mul determinant (weylLong (r + 1) F), RankOneGammaTwist.determinant_inverseTranspose,
    map_mul determinant g, determinant_weyl_ratio n r hnr,
    map_mul determinant (weylLong (n + 1) F), RankOneGammaTwist.determinant_inverseTranspose,
    hdet, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- The minus-one matrix of rank `m + 1` has determinant `(-1)^(m+1)`. -/
theorem determinant_neg_one (m : ℕ) :
    determinant (-1 : Langlands.GeneralLinear (m + 1) F) = (-1 : Fˣ) ^ (m + 1) := by
  apply Units.ext
  change Matrix.det (-1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = _
  rw [Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]
  simp

theorem character_negOne_pow_of_even (χ : Fˣ →* ℂˣ) {m : ℕ} (hm : Even m) :
    χ (-1) ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul, pow_mul, RankOneGammaTwist.character_negOne_sq, one_pow]

/-- The dual sign is the `r`-th power of the change of the minus-one scalar. -/
theorem sign_exponent (χ : Fˣ →* ℂˣ) (n r : ℕ) (hnr : n ≤ r) :
    χ (-1) ^ ((n + 1) * (r - n)) = (χ (-1) ^ (n + 1)) ^ r := by
  rw [← pow_mul]
  have h : (n + 1) * r = (n + 1) * (r - n) + n * (n + 1) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnr
    rw [Nat.add_sub_cancel_left]
    ring
  rw [h, pow_add, character_negOne_pow_of_even χ (Nat.even_mul_succ_self n), mul_one]

theorem character_negOne_mul_self (χ : Fˣ →* ℂˣ) :
    (χ (-1) : ℂ) * (χ (-1) : ℂ) = 1 := by
  simpa only [pow_two, Units.val_mul, Units.val_one] using
    congrArg Units.val (RankOneGammaTwist.character_negOne_sq χ)

end Determinants

section Models

variable {F : Type uF} [Field F] [TopologicalSpace F] (χ : Fˣ →* ℂˣ) {m : ℕ}
  {θ : upperUnipotent (m + 1) F →* ℂˣ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)

/-- The same functional on the twisted representation. -/
abbrev twisted (ℓ : functionals (upperUnipotent (m + 1) F) θ ρ) :
    functionals (upperUnipotent (m + 1) F) θ (Langlands.twist (χ.comp determinant) ρ) :=
  twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) ρ ℓ

/-- The same functional on the untwisted representation. -/
abbrev untwisted
    (ℓ : functionals (upperUnipotent (m + 1) F) θ (Langlands.twist (χ.comp determinant) ρ)) :
    functionals (upperUnipotent (m + 1) F) θ ρ :=
  untwistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) ρ ℓ

omit [TopologicalSpace F] in
/-- Coefficients of the twisted model are multiplied by `χ(det g)`. -/
theorem twisted_coefficient (ℓ : functionals (upperUnipotent (m + 1) F) θ ρ) (v : V)
    (g : Langlands.GeneralLinear (m + 1) F) :
    (modelMap (Langlands.twist (χ.comp determinant) ρ) (twisted χ ρ ℓ) v).val.val g =
      (χ (determinant g) : ℂ) * (modelMap ρ ℓ v).val.val g :=
  (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
    (determinantCharacter_unipotent χ) ρ ℓ v) g).symm

variable {χ ρ}

omit [TopologicalSpace F] in
/-- Twisting multiplies the minus-one scalar by `χ(-1)^(m+1)`. -/
theorem minusOne_twist {ℓ : functionals (upperUnipotent (m + 1) F) θ ρ} {ζ : ℂˣ}
    (h : HasModelMinusOneScalar ρ ℓ ζ) :
    HasModelMinusOneScalar (Langlands.twist (χ.comp determinant) ρ) (twisted χ ρ ℓ)
      (ζ * χ (-1) ^ (m + 1)) := by
  intro f g
  obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
  rw [twisted_coefficient, twisted_coefficient, h (modelMap ρ ℓ v) g, map_mul,
    determinant_neg_one, map_mul, map_pow]
  push_cast
  ring

omit [TopologicalSpace F] in
/-- Conversely, the untwisted model has minus-one scalar multiplied by `χ(-1)^(m+1)`. -/
theorem minusOne_untwist {ℓ : functionals (upperUnipotent (m + 1) F) θ ρ} {ζ : ℂˣ}
    (h : HasModelMinusOneScalar (Langlands.twist (χ.comp determinant) ρ) (twisted χ ρ ℓ) ζ) :
    HasModelMinusOneScalar ρ ℓ (ζ * χ (-1) ^ (m + 1)) := by
  intro f g
  obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
  have hv := h (modelMap _ (twisted χ ρ ℓ) v) g
  rw [twisted_coefficient, twisted_coefficient, map_mul, determinant_neg_one, map_mul,
    map_pow] at hv
  push_cast at hv ⊢
  have hx : (χ (determinant g) : ℂ) ≠ 0 := Units.ne_zero _
  have ha : ((χ (-1) : ℂ) ^ (m + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, sq, character_negOne_mul_self, one_pow]
  have hax : (χ (-1) : ℂ) ^ (m + 1) * (χ (determinant g) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hx
  apply mul_left_cancel₀ hax
  linear_combination hv - ((ζ : ℂ) * (χ (determinant g) : ℂ) *
    (modelMap ρ ℓ v).val.val g) * ha

end Models

section ScalarIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- Pointwise scalar comparison at equal determinants descends through both integrals. -/
theorem unequal_integral_scale {r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W₁ W₂ : WhittakerFunctions ψ r) (W₁' W₂' : InverseWhittakerFunctions ψ n)
    (c : ℂ)
    (h : ∀ (g : Langlands.GeneralLinear (r + 1) F)
      (a : Langlands.GeneralLinear (n + 1) F), determinant g = determinant a →
      W₁.val g * W₁'.val a = c * (W₂.val g * W₂'.val a)) :
    unequalRankIntegralAt j k hr ψ abv μ ν W₁ W₁' =
      fun s => c * unequalRankIntegralAt j k hr ψ abv μ ν W₂ W₂' s := by
  subst r
  funext s
  change (∫ q, ∫ x, unequalRankIntegrand ψ abv j k W₁ W₁' s x q ∂ν ∂μ) =
    c * ∫ q, ∫ x, unequalRankIntegrand ψ abv j k W₂ W₂' s x q ∂ν ∂μ
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  induction q using Quotient.inductionOn with
  | h a =>
    simp only [unequalRankIntegrand_mk]
    rw [h _ _ (determinant_unequalRankMatrix j k a x)]
    ring

omit [MeasurableSpace F] in
/-- Equal-rank pointwise comparison keeps the same Schwartz--Bruhat test. -/
theorem equal_integral_eq (μ : Measure (LeftUnipotentQuotient n F))
    (W₁ W₂ : WhittakerFunctions ψ n) (W₁' W₂' : InverseWhittakerFunctions ψ n)
    (h : ∀ g, W₁.val g * W₁'.val g = W₂.val g * W₂'.val g)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankIntegral ψ abv μ W₁ W₁' Φ = equalRankIntegral ψ abv μ W₂ W₂' Φ := by
  funext s
  unfold equalRankIntegral
  apply integral_congr_ae
  filter_upwards [] with q
  induction q using Quotient.inductionOn with
  | h a =>
    simp only [equalRankIntegrand_mk]
    rw [h a]

end ScalarIntegrals

section Products

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (v : V) (z : W)

/-- Forward coefficient products agree whenever the determinants agree. -/
theorem forward_product (g : Langlands.GeneralLinear (r + 1) F)
    (a : Langlands.GeneralLinear (n + 1) F) (hdet : determinant g = determinant a) :
    (modelMap (Langlands.twist (χ.comp determinant) π) (twisted χ π ℓ) v).val.val g *
        (modelMap σ ℓ' z).val.val a =
    (modelMap π ℓ v).val.val g *
      (modelMap (Langlands.twist (χ.comp determinant) σ) (twisted χ σ ℓ') z).val.val a := by
  rw [twisted_coefficient, twisted_coefficient, hdet]
  ring

variable [IsTopologicalRing F]

/-- The translated dual products differ by the Weyl sign. -/
theorem unequal_dual_product (hn : n < r)
    (g : Langlands.GeneralLinear (r + 1) F) (a : Langlands.GeneralLinear (n + 1) F)
    (hdet : determinant g = determinant a) :
    (translateWhittaker (ψ.scale (-1)) r
      (firstDualFunction ψ r (modelMap (Langlands.twist (χ.comp determinant) π)
        (twisted χ π ℓ) v).val) (blockWeylAt n r hn)).val g *
      (secondDualFunction ψ n (modelMap σ ℓ' z).val).val a =
    (χ (-1) : ℂ) ^ ((n + 1) * (r - n)) *
      ((translateWhittaker (ψ.scale (-1)) r
        (firstDualFunction ψ r (modelMap π ℓ v).val) (blockWeylAt n r hn)).val g *
        (secondDualFunction ψ n (modelMap (Langlands.twist (χ.comp determinant) σ)
          (twisted χ σ ℓ') z).val).val a) := by
  simp only [translateWhittaker_apply, firstDualFunction_apply, secondDualFunction_apply,
    twisted_coefficient]
  rw [determinant_dual_arguments n r hn g a hdet, map_mul, map_pow]
  push_cast
  ring

/-- In equal rank the dual products agree. -/
theorem equal_dual_product
    {U : Type uW} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) U)
    (L' : glInverseFunctionals ψ r ρ) (u : U) (g : Langlands.GeneralLinear (r + 1) F) :
    (firstDualFunction ψ r (modelMap (Langlands.twist (χ.comp determinant) π)
      (twisted χ π ℓ) v).val).val g *
      (secondDualFunction ψ r (modelMap ρ L' u).val).val g =
    (firstDualFunction ψ r (modelMap π ℓ v).val).val g *
      (secondDualFunction ψ r (modelMap (Langlands.twist (χ.comp determinant) ρ)
        (twisted χ ρ L') u).val).val g := by
  simp only [firstDualFunction_apply, secondDualFunction_apply]
  exact forward_product ψ χ π ρ ℓ L' v u _ _ rfl

end Products

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
  (abv : AbsoluteValue F ℝ)
  {r n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (v : V) (z : W)

omit [IsTopologicalRing F] in
/-- Every forward block integral agrees. -/
theorem unequal_forward (j k : ℕ) (hr : r = n + (j + k + 1))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)) :
    unequalRankIntegralAt j k hr ψ abv μ ν
      (modelMap (Langlands.twist (χ.comp determinant) π) (twisted χ π ℓ) v).val
      (modelMap σ ℓ' z).val =
    unequalRankIntegralAt j k hr ψ abv μ ν (modelMap π ℓ v).val
      (modelMap (Langlands.twist (χ.comp determinant) σ) (twisted χ σ ℓ') z).val := by
  simpa only [one_mul] using unequal_integral_scale ψ abv j k hr μ ν _ _ _ _ 1
    (fun g a hd => by simpa only [one_mul] using forward_product ψ χ π σ ℓ ℓ' v z g a hd)

/-- Every dual block integral acquires the sign `χ(-1)^((n+1)(r-n))`. -/
theorem unequal_dual (hn : n < r) (j k : ℕ) (hr : r = n + (j + k + 1))
    (ν : AdditiveHaarMeasure F) :
    dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν
      (Langlands.twist (χ.comp determinant) π) σ (twisted χ π ℓ) ℓ'
      (modelMap _ _ v) (modelMap _ _ z) =
    fun s => (χ (-1) : ℂ) ^ ((n + 1) * (r - n)) *
      dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν π
        (Langlands.twist (χ.comp determinant) σ) ℓ (twisted χ σ ℓ')
        (modelMap _ _ v) (modelMap _ _ z) s :=
  unequal_integral_scale (ψ.scale (-1)) abv k j (by omega) μ
    (rectangularMeasure ν k (n + 1)) _ _ _ _ _
    (unequal_dual_product ψ χ π σ ℓ ℓ' v z hn)

end Integrals

section EqualIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) (v : V) (z : W)

omit [IsTopologicalRing F] in
/-- The equal-rank forward integral keeps every test function. -/
theorem equal_forward (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankModelIntegral ψ abv μ (Langlands.twist (χ.comp determinant) π) σ
      (twisted χ π ℓ) ℓ' (modelMap _ _ v) (modelMap _ _ z) Φ =
    equalRankModelIntegral ψ abv μ π (Langlands.twist (χ.comp determinant) σ) ℓ
      (twisted χ σ ℓ') (modelMap _ _ v) (modelMap _ _ z) Φ :=
  equal_integral_eq ψ abv μ _ _ _ _
    (fun g => forward_product ψ χ π σ ℓ ℓ' v z g g rfl) Φ

/-- The equal-rank dual integral keeps every test function. -/
theorem equal_dual (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    dualEqualRankModelIntegral ψ abv μ (Langlands.twist (χ.comp determinant) π) σ
      (twisted χ π ℓ) ℓ' (modelMap _ _ v) (modelMap _ _ z) Φ =
    dualEqualRankModelIntegral ψ abv μ π (Langlands.twist (χ.comp determinant) σ) ℓ
      (twisted χ σ ℓ') (modelMap _ _ v) (modelMap _ _ z) Φ :=
  equal_integral_eq (ψ.scale (-1)) abv μ _ _ _ _
    (fun g => equal_dual_product ψ χ π ℓ v σ ℓ' z g) Φ

end EqualIntegrals

end Langlands.RankinSelberg.PairGammaTwistExchange
