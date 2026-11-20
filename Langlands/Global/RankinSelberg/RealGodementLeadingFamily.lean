import Langlands.Global.RankinSelberg.RealGodementJointConvergence
import Langlands.Global.RankinSelberg.RealGodementOpenCellModel

/-! # Entire continuation in the leading real Godement character -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Matrix
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-- The first-column value of a real Godement section as a function of the
leading inducing exponent, in the open-cell translate convention. -/
def godementLeadingFamily (D : RealQuotientMeasureData t) (a : ℝˣ) (Φ : 𝓢(X, ℂ))
    (W : G → ℂ) (p : Fin 2) (g : H) (z : ℂ) : ℂ :=
  godementColumnValue D a Φ W (charData p z) (weylLong (t + 2) ℝ * g)

private theorem differentiable_determinantWeight_charData {n : ℕ} (p : Fin 2) (s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    Differentiable ℂ (fun z : ℂ => determinantWeight (charData p z) s g) := by
  let x := determinant g
  let b : ℂ := (|(x : ℝ)| : ℝ)
  let sign : ℂ := ((((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ)) ^ p.val
  let : NeZero b := ⟨by
    change ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0
    exact_mod_cast abs_ne_zero.mpr x.ne_zero⟩
  have h (z : ℂ) : determinantWeight (charData p z) s g = (sign * b ^ z) * b ^ s := by
    change ((charData p z).character x : ℂ) * b ^ s = _
    rw [(charData p z).character_eq]
    rfl
  simp_rw [h]
  exact ((differentiable_const_cpow_of_neZero b).const_mul sign).mul_const (b ^ s)

/-- The entire family is defined for any supplied uniform lower coefficient. -/
theorem differentiable_godementLeadingFamily (D : RealQuotientMeasureData t) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) {ds : List RealBlock} {W : G → ℂ}
    (hW : W ∈ realUniformWhittakerModel t ds (-a)) (p : Fin 2) (g : H) :
    Differentiable ℂ (godementLeadingFamily D a Φ W p g) := by
  let g' := weylLong (t + 2) ℝ * g
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  have hI := (columnMellin_convergence_of_mem_model D.groupHaar a (rectangularTranslate 1 g' Φ)
    hW p.val).2
  have hM := hI.comp (differentiable_id.add_const ((t : ℂ) / 2))
  exact (differentiable_determinantWeight_charData p (((t : ℂ) + 1) / 2) g').mul hM

private theorem characterData_eq_of_parameters (b c : RealCharacterData)
    (hp : b.parity = c.parity) (he : b.exponent = c.exponent) : b = c := by
  have hχ : b.character = c.character := by
    ext x
    rw [b.character_eq, c.character_eq, hp, he]
  cases b
  cases c
  cases hp
  cases he
  cases hχ
  rfl

/-- Reflection of the entire leading-character column values for the two
opposite-sign lower coefficients. -/
theorem godementLeadingFamily_reflection (D : RealQuotientMeasureData t) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) {ds ds' : List RealBlock} {W : G → ℂ}
    (hW : W ∈ realUniformWhittakerModel t ds (-a))
    (hW' : ArchimedeanLocal.dualFunction (t + 1) W ∈ realUniformWhittakerModel t ds' a)
    (p : Fin 2) (g : H) (z : ℂ) :
    godementLeadingFamily D a Φ W p (weylInverseTranspose (t + 2) ℝ g) z =
      (((-1 : ℂ) ^ p.val) ^ (t + 1)) *
        godementLeadingFamily D (-a) (realRectangularSchwartzFourier a Φ)
          (ArchimedeanLocal.dualFunction (t + 1) W) p g (-z) := by
  let w := weylLong (t + 2) ℝ
  have hArg : w * weylInverseTranspose (t + 2) ℝ g = weylInverseTranspose (t + 2) ℝ (w * g) := by
    simp only [weylInverseTranspose_apply, map_mul, inverseTranspose_weylLong, w]
  have hInv : (charData p z).inverse = charData p (-z) :=
    characterData_eq_of_parameters _ _ rfl rfl
  have hSign : ((charData p z).character ((-1 : ℝˣ) ^ (t + 1)) : ℂ) = (((-1 : ℂ) ^ p.val) ^ (t + 1)) := by
    simp only [map_pow, Units.val_pow_eq_pow_val, charData_character_apply,
      Units.val_neg, Units.val_one, charFun_neg_one]
  have h := (realGodementColumnReflection t D a Φ (charData p z) ds ds' W (w * g) hW hW').2.2
  unfold godementLeadingFamily
  rw [hArg]
  simpa only [hInv, hSign] using h

/-- For a strictly dominant K-finite lower vector and a compact full-row-rank
Schwartz test, the entire first-column family agrees with the real open-cell
Jacquet integral throughout the dominant half-plane of the leading exponent. -/
def RealGodementLeadingFamilyStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock)
    (f : Automorphic.realStandardKFinite (t + 1) ds),
    IsStrictlyDominant (realPositionExponent ds) t →
    ∀ (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
      (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
    ∀ (g : Langlands.GeneralLinear (t + 2) ℝ),
      Differentiable ℂ (godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g) ∧
      ∀ z : ℂ, (realPositionExponent ds 0).re < z.re →
        godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g z =
          additiveJacquetIntegral a (sectionValue D.groupHaar (charData p z) f.val Φ) g

theorem realGodementLeadingFamily : RealGodementLeadingFamilyStatement := by
  intro t D a p ds f hDom S hS hRank Φ hΦS g
  have hW := realGodementOpenCellModel t ds a hDom f
  refine ⟨differentiable_godementLeadingFamily D a Φ hW p g, ?_⟩
  intro z hz
  let c := charData p z
  have hUpper : IsStrictlyDominant (realPositionExponent (.character c :: ds)) (t + 1) := by
    intro j hj
    cases j with
    | zero => exact hz
    | succ j => exact hDom j (Nat.lt_of_succ_lt_succ hj)
  have hi := realGodementJointConvergence t D a c ds f.val f.property.1.1 hUpper S hS hRank Φ hΦS g
  exact (realGodementAdditiveJacquet t D a c f.val Φ g hi).2.2.symm

end Langlands.Global.RankinSelbergGlobal.RealGodement
