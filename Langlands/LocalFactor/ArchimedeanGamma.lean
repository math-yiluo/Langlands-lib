import Langlands.LocalFactor.ArchimedeanScaling

/-!
# Gamma factors of presented archimedean characters

The inverse data uses the actual pointwise inverse character. Evaluation keeps
both L-factors regular and retains the supplied character and Haar scales.
-/

noncomputable section

namespace Langlands.LocalFactor

namespace ReciprocalEntire

/-- The common domain on which the original and reflected factors are regular. -/
def ReflectedRegularAt (F G : ReciprocalEntire) (s : ℂ) : Prop :=
  F.denominator s ≠ 0 ∧ G.denominator (1 - s) ≠ 0

/-- Inputs for the ratio `G(1-s)/F(s)`, excluding both individual pole sets. -/
def ReflectedRegularPoint (F G : ReciprocalEntire) :=
  {s : ℂ // F.ReflectedRegularAt G s}

/-- The reflected ratio of the existing unit-valued evaluations. -/
def reflectedRatio (F G : ReciprocalEntire) (s : F.ReflectedRegularPoint G) : ℂˣ :=
  G.eval ⟨1 - s.val, s.property.2⟩ / F.eval ⟨s.val, s.property.1⟩

theorem coe_reflectedRatio (F G : ReciprocalEntire) (s : F.ReflectedRegularPoint G) :
    (F.reflectedRatio G s : ℂ) = F.denominator s.val / G.denominator (1 - s.val) := by
  rw [reflectedRatio, Units.val_div_eq_div_val,
    G.coe_eval ⟨1 - s.val, s.property.2⟩, F.coe_eval ⟨s.val, s.property.1⟩]
  exact inv_div_inv _ _

theorem reflectedRegularAt_iff (F G : ReciprocalEntire) (s : ℂ) :
    F.ReflectedRegularAt G s ↔ ¬F.IsPole s ∧ ¬G.IsPole (1 - s) := Iff.rfl

/-- Reflection exchanges the two regular factors. -/
def reflectedRegularPointEquiv (F G : ReciprocalEntire) :
    F.ReflectedRegularPoint G ≃ G.ReflectedRegularPoint F where
  toFun s := ⟨1 - s.val, s.property.2, by simpa using s.property.1⟩
  invFun s := ⟨1 - s.val, s.property.2, by simpa using s.property.1⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

theorem reflectedRatio_reflection (F G : ReciprocalEntire)
    (s : F.ReflectedRegularPoint G) :
    G.reflectedRatio F (F.reflectedRegularPointEquiv G s) =
      (F.reflectedRatio G s)⁻¹ := by
  apply Units.ext
  rw [coe_reflectedRatio, Units.val_inv_eq_inv_val, coe_reflectedRatio]
  change G.denominator (1 - s.val) / F.denominator (1 - (1 - s.val)) = _
  simp only [sub_sub_cancel, inv_div]

end ReciprocalEntire

namespace Archimedean

namespace RealCharacterData

/-- The actual inverse real character has the same parity and opposite exponent. -/
def inverse (d : RealCharacterData) : RealCharacterData where
  character := d.character⁻¹
  parity := d.parity
  exponent := -d.exponent
  character_eq := by
    intro x
    change ((d.character x)⁻¹ : ℂˣ).val = _
    rw [Units.val_inv_eq_inv_val]
    have hsign :
        (((((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ))⁻¹) =
          (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ) := by
      rcases lt_or_gt_of_ne x.ne_zero with hx | hx
      · simp [abs_of_neg hx, x.ne_zero]
      · simp [abs_of_pos hx, x.ne_zero]
    rw [d.character_eq, mul_inv, ← inv_pow, hsign, Complex.cpow_neg]

@[simp]
theorem inverse_character (d : RealCharacterData) : d.inverse.character = d.character⁻¹ := rfl

@[simp]
theorem inverse_inverse (d : RealCharacterData) : d.inverse.inverse = d := by
  cases d with
  | mk ch p e h => simp only [inverse, inv_inv ch, neg_neg]

@[simp]
theorem inverse_lFactor (d : RealCharacterData) :
    d.inverse.lFactor = gammaReal.shift (-d.exponent + (d.parity.val : ℂ)) := rfl

/-- Both the character L-factor and its reflected inverse-character factor
are regular at this spectral parameter. -/
def GammaRegularAt (d : RealCharacterData) (s : ℂ) : Prop :=
  d.lFactor.ReflectedRegularAt d.inverse.lFactor s

abbrev GammaRegularPoint (d : RealCharacterData) :=
  d.lFactor.ReflectedRegularPoint d.inverse.lFactor

theorem gammaRegularAt_iff (d : RealCharacterData) (s : ℂ) :
    d.GammaRegularAt s ↔
      (¬∃ n : ℕ, s + (d.exponent + (d.parity.val : ℂ)) = -(2 * (n : ℂ))) ∧
      (¬∃ n : ℕ, (1 - s) + (-d.exponent + (d.parity.val : ℂ)) =
        -(2 * (n : ℂ))) := by
  change (¬d.lFactor.IsPole s ∧ ¬d.inverse.lFactor.IsPole (1 - s)) ↔ _
  rw [d.lFactor_isPole, d.inverse.lFactor_isPole]
  rfl

/-- The unit `L(1-s,chi inverse)/L(s,chi)`. -/
def gammaLRatio (d : RealCharacterData) (s : d.GammaRegularPoint) : ℂˣ :=
  d.lFactor.reflectedRatio d.inverse.lFactor s

/-- Gamma for the actual scaled plus character and scaled real Haar measure. -/
def gammaValue (d : RealCharacterData) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : d.GammaRegularPoint) : ℂˣ :=
  d.epsilon a c hc s.val * d.gammaLRatio s

theorem coe_gammaValue (d : RealCharacterData) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : d.GammaRegularPoint) :
    (d.gammaValue a c hc s : ℂ) =
      (d.epsilon a c hc s.val : ℂ) *
        (d.lFactor.denominator s.val / d.inverse.lFactor.denominator (1 - s.val)) := by
  rw [gammaValue, Units.val_mul, gammaLRatio, ReciprocalEntire.coe_reflectedRatio]

theorem gammaValue_standard (d : RealCharacterData) (s : d.GammaRegularPoint) :
    d.gammaValue 1 1 zero_lt_one s = d.standardEpsilon * d.gammaLRatio s := by
  rw [gammaValue, epsilon_standard]

theorem gammaValue_measure_scale (d : RealCharacterData) (a : ℝˣ)
    (c b : NNReal) (hc : 0 < c) (hb : 0 < b) (s : d.GammaRegularPoint) :
    (d.gammaValue a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) * (d.gammaValue a c hc s : ℂ) := by
  simp only [gammaValue, Units.val_mul]
  rw [d.epsilon_measure_scale a c b hc hb s.val]
  exact mul_assoc _ _ _

end RealCharacterData

namespace ComplexCharacterData

/-- The actual inverse complex character has opposite weight and exponent. -/
def inverse (d : ComplexCharacterData) : ComplexCharacterData where
  character := d.character⁻¹
  weight := -d.weight
  exponent := -d.exponent
  character_eq := by
    intro z
    change ((d.character z)⁻¹ : ℂˣ).val = _
    rw [Units.val_inv_eq_inv_val]
    rw [d.character_eq, mul_inv, zpow_neg, mul_neg, Complex.cpow_neg]

@[simp]
theorem inverse_character (d : ComplexCharacterData) :
    d.inverse.character = d.character⁻¹ := rfl

@[simp]
theorem inverse_inverse (d : ComplexCharacterData) : d.inverse.inverse = d := by
  cases d with
  | mk ch p e h => simp only [inverse, inv_inv ch, neg_neg]

@[simp]
theorem inverse_lFactor (d : ComplexCharacterData) :
    d.inverse.lFactor = gammaComplex.shift (-d.exponent + (d.weight.natAbs : ℂ) / 2) := by
  simp [lFactor, inverse, complexTateL]

/-- The common regular domain of the complex character and reflected inverse. -/
def GammaRegularAt (d : ComplexCharacterData) (s : ℂ) : Prop :=
  d.lFactor.ReflectedRegularAt d.inverse.lFactor s

abbrev GammaRegularPoint (d : ComplexCharacterData) :=
  d.lFactor.ReflectedRegularPoint d.inverse.lFactor

theorem gammaRegularAt_iff (d : ComplexCharacterData) (s : ℂ) :
    d.GammaRegularAt s ↔
      (¬∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ)) ∧
      (¬∃ n : ℕ, (1 - s) + (-d.exponent + (d.weight.natAbs : ℂ) / 2) =
        -(n : ℂ)) := by
  change (¬d.lFactor.IsPole s ∧ ¬d.inverse.lFactor.IsPole (1 - s)) ↔ _
  simp only [lFactor_isPole, inverse, Int.natAbs_neg]

/-- The unit `L(1-s,chi inverse)/L(s,chi)` for a complex character. -/
def gammaLRatio (d : ComplexCharacterData) (s : d.GammaRegularPoint) : ℂˣ :=
  d.lFactor.reflectedRatio d.inverse.lFactor s

/-- Gamma for the actual scaled trace character and scaled complex Haar measure. -/
def gammaValue (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : d.GammaRegularPoint) : ℂˣ :=
  d.epsilon a c hc s.val * d.gammaLRatio s

theorem coe_gammaValue (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : d.GammaRegularPoint) :
    (d.gammaValue a c hc s : ℂ) =
      (d.epsilon a c hc s.val : ℂ) *
        (d.lFactor.denominator s.val / d.inverse.lFactor.denominator (1 - s.val)) := by
  rw [gammaValue, Units.val_mul, gammaLRatio, ReciprocalEntire.coe_reflectedRatio]

theorem gammaValue_standard (d : ComplexCharacterData) (s : d.GammaRegularPoint) :
    d.gammaValue 1 1 zero_lt_one s = d.standardEpsilon * d.gammaLRatio s := by
  rw [gammaValue, epsilon_standard]

theorem gammaValue_measure_scale (d : ComplexCharacterData) (a : ℂˣ)
    (c b : NNReal) (hc : 0 < c) (hb : 0 < b) (s : d.GammaRegularPoint) :
    (d.gammaValue a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) * (d.gammaValue a c hc s : ℂ) := by
  simp only [gammaValue, Units.val_mul]
  rw [d.epsilon_measure_scale a c b hc hb s.val]
  exact mul_assoc _ _ _

end ComplexCharacterData

end Archimedean
end Langlands.LocalFactor
