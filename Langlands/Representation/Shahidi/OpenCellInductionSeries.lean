import Langlands.Representation.Shahidi.OpenCellThreeBlockFubini

/-! # The two generating series of the three-block coefficients

For the block sizes `(1, d + 1, t + 1)` let `A(D, e₁)` be the open-cell integral at `1` for the
`(d + 2, t + 1)` parabolic of the degree-`D` piece of `δ^(1/2) J_(e₁) ⊗ W°_c`, where `J_(e₁)` is
the Jacquet function of the degree-`e₁` piece of the `(1, d + 1)` section with parameters
`(a₁, a')` at `s = 0`, and let `ψ` have conductor `𝒪`. If the shell identities hold for the
ranks `(0, d)`, then for small `X`
`∑_(e₁) X^(e₁) A(D, e₁) = ∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) · P_D(X a₁, a'; c)`, where `P_D` is the
degree-`D` shell sum of the `(d + 2, t + 1)` section. If the shell identities hold for the
ranks `(d, t)`, then by transitivity and the rank-one shells, for each `e₁ ≥ 0` and small
`Z`, `∑_D A(D, e₁) Z^D = Z^(e₁) ∏_(j,l) (1 - Z a'_j c_l⁻¹ q⁻¹) · c_(e₁)(a₁; (Z a', c))`,
with `c_(e₁)` the degree-`e₁` coefficient of the rank-one product; `A(D, e₁)` vanishes for
`e₁` outside `[0, d + t + 2]` and for `D < 0`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocISTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocISValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocISLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocIST2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocISSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocISMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocISBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section Linear

variable {r t : ℕ}

theorem degreePiece_const_mul (z : ℂ) (D : ℤ)
    (Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) :
    degreePiece hϖ D (fun m₁ m₂ => z * Φ m₁ m₂) = fun m₁ m₂ => z * degreePiece hϖ D Φ m₁ m₂ := by
  funext m₁ m₂
  simp only [degreePiece]
  split_ifs <;> simp

theorem jacquetFunction_degreePiece_const_mul (z : ℂ) (D : ℤ)
    (Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetFunction ψ hϖ (degreePiece hϖ D (fun m₁ m₂ => z * Φ m₁ m₂)) g =
      z * jacquetFunction ψ hϖ (degreePiece hϖ D Φ) g := by
  rw [degreePiece_const_mul, jacquetFunction, jacquetFunction, ← integral_const_mul]
  congr 1
  funext Y
  simp only [jacquetIntegrandAt_apply, liftFunction_const_mul]
  ring

theorem baseValue_eq_mul (t' : ℕ) (D : ℤ) (Ψ : Langlands.GeneralLinear (t' + 1) K.Carrier → ℂ) :
    Base.baseValue ϖ t' D Ψ =
      Base.baseValue ϖ t' D (fun _ => 1) * Ψ (Iwasawa.torus ϖ (Base.baseKappa t' D.toNat)) := by
  unfold Base.baseValue
  split_ifs <;> ring

theorem baseValue_of_lt (t' : ℕ) {D : ℤ} (hD : (t' : ℤ) + 1 < D)
    (Ψ : Langlands.GeneralLinear (t' + 1) K.Carrier → ℂ) : Base.baseValue ϖ t' D Ψ = 0 := by
  unfold Base.baseValue
  rw [ite_eq_right_iff.2 fun h => absurd h (by omega)]

end Linear

section Coefficients

variable (d t : ℕ) (a₁ : Fin (0 + 1) → ℂˣ) (a' : Fin (d + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ)

/-- The three-block coefficient `A(D, e₁)`. -/
def threeCoef (D e₁ : ℤ) : ℂ :=
  jacquetFunction ψ hϖ (degreePiece hϖ D (prodΦ (r := 0 + 1 + d) (t := t) 0
    (jacquetFunction ψ hϖ (degreePiece hϖ e₁ (Base.fullΦ ψ hϖ a₁ a' 0)))
    (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
      K.canonicalTopologicalData.residueCardinality c))) 1

theorem isLeviInvariant_threeLeft (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (e₁ : ℤ) :
    IsLeviInvariant (prodΦ (r := 0 + 1 + d) (t := t) 0
      (jacquetFunction ψ hϖ (degreePiece hϖ e₁ (Base.fullΦ ψ hϖ a₁ a' 0)))
      (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c)) :=
  isLeviInvariant_prodΦ (r := 0 + 1 + d) (t := t) 0
    (fun g k hk => jacquetFunction_mul_integral ψ hϖ
      (isLeviInvariant_degreePiece hϖ e₁ (Base.isLeviInvariant_fullΦ hϖ hψ a₁ a' 0)) g k hk)
    (whittaker_mul_integral' hϖ hψ c)

theorem isLeviInvariant_threeRight (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (e : ℤ) :
    IsLeviInvariant (prodΦ (r := 0) (t := d + 1 + t) 0
      (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a₁)
      (jacquetFunction ψ hϖ (degreePiece hϖ e (Base.fullΦ ψ hϖ a' c 0)))) :=
  isLeviInvariant_prodΦ (r := 0) (t := d + 1 + t) 0 (whittaker_mul_integral' hϖ hψ a₁)
    (fun g k hk => jacquetFunction_mul_integral ψ hϖ
      (isLeviInvariant_degreePiece hϖ e (Base.isLeviInvariant_fullΦ hϖ hψ a' c 0)) g k hk)

theorem threeCoef_eq (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (D e₁ : ℤ) :
    threeCoef ψ hϖ d t a₁ a' c D e₁ =
      jacquetFunction ψ hϖ (degreePiece hϖ e₁ (prodΦ (r := 0) (t := d + 1 + t) 0
        (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
          K.canonicalTopologicalData.residueCardinality a₁)
        (jacquetFunction ψ hϖ (degreePiece hϖ (D - e₁) (Base.fullΦ ψ hϖ a' c 0))))) 1 :=
  jacquetFunction_threeBlock ψ hϖ d t a₁ a' c D e₁ hψ

theorem threeCoef_of_neg_left (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    {D : ℤ} (hD : D < 0) (e₁ : ℤ) : threeCoef ψ hϖ d t a₁ a' c D e₁ = 0 :=
  jacquetFunction_degreePiece_one_of_neg ψ hϖ hψ (isLeviInvariant_threeLeft ψ hϖ d t a₁ a' c hψ e₁) hD

theorem threeCoef_of_neg_right (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (D : ℤ) {e₁ : ℤ} (he : e₁ < 0) : threeCoef ψ hϖ d t a₁ a' c D e₁ = 0 := by
  rw [threeCoef_eq ψ hϖ d t a₁ a' c hψ]
  exact jacquetFunction_degreePiece_one_of_neg ψ hϖ hψ
    (isLeviInvariant_threeRight ψ hϖ d t a₁ a' c hψ (D - e₁)) he

theorem isWhittakerType_jacquetFunction (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (e : ℤ) : Base.IsWhittakerType (t := d + 1 + t) ψ
      (jacquetFunction ψ hϖ (degreePiece hϖ e (Base.fullΦ (r := d) (t := t) ψ hϖ a' c 0))) :=
  ⟨fun u g => jacquetFunction_unipotent_mul ψ hϖ
      (isLeviInvariant_degreePiece hϖ e (Base.isLeviInvariant_fullΦ hϖ hψ a' c 0))
      (isLeviEquivariant_degreePiece hϖ e (isLeviEquivariant_fullΦ hϖ hψ a' c 0)) u g,
    fun g k hk => jacquetFunction_mul_integral ψ hϖ
      (isLeviInvariant_degreePiece hϖ e (Base.isLeviInvariant_fullΦ hϖ hψ a' c 0)) g k hk⟩

theorem threeCoef_eq_base (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (D : ℤ) (e₁ : ℕ) :
    threeCoef ψ hϖ d t a₁ a' c D e₁ =
      Base.baseCoef (K := K) (d + 1 + t) e₁ a₁ 0 * Base.baseValue ϖ (d + 1 + t) e₁
        (jacquetFunction ψ hϖ (degreePiece hϖ (D - e₁) (Base.fullΦ ψ hϖ a' c 0))) := by
  rw [threeCoef_eq ψ hϖ d t a₁ a' c hψ]
  exact jacquetFunction_degreePiece_prodΦ_rankOne hϖ hψ a₁ 0
    (isWhittakerType_jacquetFunction ψ hϖ d t a' c hψ (D - e₁)) e₁

theorem threeCoef_of_lt (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (D : ℤ) {e₁ : ℕ} (he : d + 1 + t + 1 < e₁) : threeCoef ψ hϖ d t a₁ a' c D e₁ = 0 := by
  rw [threeCoef_eq_base ψ hϖ d t a₁ a' c hψ]
  erw [baseValue_of_lt (d + 1 + t) (by push_cast; omega), mul_zero]

/-- **The series in the outer degree (route through the `(d + 1, t + 1)` block)**, for `ψ` of
conductor `𝒪`. -/
theorem threeCoef_series_right (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (hB : CoreAt ψ hϖ d t) (e₁ : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Z : ℂˣ, ‖(Z : ℂ)‖ < ρ →
      HasSum (fun D : ℕ => threeCoef ψ hϖ d t a₁ a' c D e₁ * (Z : ℂ) ^ D)
        ((Z : ℂ) ^ e₁ *
          (∏ x, (1 - (Z : ℂ) * pairParameter K.canonicalTopologicalData.residueCardinality a' c 0 x)) *
          shellCoefficient (pairParameter K.canonicalTopologicalData.residueCardinality a₁
            (Fin.append (m := d + 1) (n := t + 1) (fun j => Z * a' j) c) 0) e₁) := by
  obtain ⟨ρ, hρ, hg⟩ := exists_hasSum_degreePiece_of_core hϖ hψ hB a' c
  refine ⟨ρ, hρ, fun Z hZ => ?_⟩
  set β := Fin.append (m := d + 1) (n := t + 1) (fun j => Z * a' j) c with hβ
  set κ : Langlands.GeneralLinear (d + 1 + t + 1) K.Carrier :=
    Iwasawa.torus ϖ (Base.baseKappa (d + 1 + t) e₁) with hκ
  have h1 := hg Z hZ κ
  set B := Base.baseValue ϖ (d + 1 + t) (e₁ : ℤ) (fun _ => (1 : ℂ)) with hB'
  set C := Base.baseCoef (K := K) (d + 1 + t) e₁ a₁ 0 * B with hC
  have h2 := h1.mul_left (C * (Z : ℂ) ^ (e₁ : ℤ))
  have h3 : HasSum (fun D : ℤ => threeCoef ψ hϖ d t a₁ a' c D e₁ * (Z : ℂ) ^ D)
      (C * (Z : ℂ) ^ (e₁ : ℤ) *
        ((∏ x, (1 - (Z : ℂ) * pairParameter K.canonicalTopologicalData.residueCardinality a' c 0 x)) *
          GeneralLinear.Spherical.sphericalWhittaker (n := d + 1 + t) hϖ
            (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (d + 1 + t))
            K.canonicalTopologicalData.residueCardinality β κ)) := by
    rw [← (Equiv.addLeft (e₁ : ℤ)).hasSum_iff]
    convert h2 using 1
    funext e
    simp only [Function.comp_apply, Equiv.coe_addLeft]
    rw [threeCoef_eq_base ψ hϖ d t a₁ a' c hψ]
    erw [baseValue_eq_mul (d + 1 + t) (e₁ : ℤ)]
    rw [show (e₁ : ℤ) + e - e₁ = e by ring, zpow_add₀ Z.ne_zero, Int.toNat_natCast]
    ring
  have h4 := hasSum_nat_of_hasSum_int (f := fun D : ℤ => threeCoef ψ hϖ d t a₁ a' c D e₁ * (Z : ℂ) ^ D)
    (fun n hn => by rw [threeCoef_of_neg_left ψ hϖ d t a₁ a' c hψ hn, zero_mul]) h3
  have h5 := h4
  simp only [zpow_natCast] at h5
  have hbase := Base.baseCoef_mul_baseValue (t := d + 1 + t) hϖ hψ a₁ β 0 e₁
  erw [baseValue_eq_mul (d + 1 + t) (e₁ : ℤ)] at hbase
  rw [Int.toNat_natCast] at hbase
  convert h5 using 1
  rw [← hbase, hC]
  ring

/-- **The series in the inner degree (route through the `(1, d + 1)` block)**, for `ψ` of
conductor `𝒪`. -/
theorem threeCoef_series_left (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (hA : CoreAt ψ hϖ 0 d) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ X : ℂˣ, ‖(X : ℂ)‖ < r₀ → ∀ D : ℤ,
      HasSum (fun e₁ : ℤ => (X : ℂ) ^ e₁ * threeCoef ψ hϖ d t a₁ a' c D e₁)
        ((∏ x, (1 - (X : ℂ) * pairParameter K.canonicalTopologicalData.residueCardinality a₁ a' 0 x)) *
          jacquetFunction ψ hϖ (degreePiece hϖ D (Base.fullΦ (r := 0 + 1 + d) (t := t) ψ hϖ
            (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0)) 1) := by
  obtain ⟨r₀, hr₀, hg⟩ := exists_hasSum_degreePiece_of_core hϖ hψ hA a₁ a'
  refine ⟨r₀, hr₀, fun X hX D => ?_⟩
  set Pr := ∏ x, (1 - (X : ℂ) * pairParameter K.canonicalTopologicalData.residueCardinality a₁ a' 0 x)
    with hPr
  have hpt : ∀ m₁ m₂, HasSum (fun e₁ : ℤ => (X : ℂ) ^ e₁ * prodΦ (r := 0 + 1 + d) (t := t) 0
      (jacquetFunction ψ hϖ (degreePiece hϖ e₁ (Base.fullΦ ψ hϖ a₁ a' 0)))
      (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c) m₁ m₂)
      (Pr * Base.fullΦ (r := 0 + 1 + d) (t := t) ψ hϖ
        (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0 m₁ m₂) := by
    intro m₁ m₂
    have h := ((hg X hX m₁).mul_left (((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^
      ((1 : ℂ) / 2 + 0 / ((0 + 1 + d + t + 2 : ℕ) : ℂ)))).mul_right
      (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c m₂)
    convert h using 1
    · funext e₁
      simp only [prodΦ]
      ring
    · simp only [Base.fullΦ]
      ring
  have hΦ : IsLeviInvariant (fun m₁ m₂ => Pr * Base.fullΦ (r := 0 + 1 + d) (t := t) ψ hϖ
      (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0 m₁ m₂) := by
    intro m₁ μ₁ m₂ μ₂ h₁ h₂
    simp only [Base.isLeviInvariant_fullΦ hϖ hψ _ c 0 m₁ μ₁ m₂ μ₂ h₁ h₂]
  have h := hasSum_jacquetFunction_degreePiece_one_of_hasSum ψ hϖ hψ
    (fun e₁ => isLeviInvariant_threeLeft ψ hϖ d t a₁ a' c hψ e₁) hΦ (fun e₁ => (X : ℂ) ^ e₁) hpt D
  rw [jacquetFunction_degreePiece_const_mul] at h
  exact h

end Coefficients

end Langlands.Shahidi.OpenCell
