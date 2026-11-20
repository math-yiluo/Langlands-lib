import Langlands.Global.RankinSelberg.RealGodementLeadingFamily

/-! # Entire leading-exponent Godement values with smooth lower inputs -/

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

open GramFormula PartialJacquet RealJacquetFrobenius RealPrincipalSeries

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

theorem regular_additiveJacquetIntegral (a : ℝˣ) {ds : List RealBlock}
    (hDom : IsStrictlyDominant (realPositionExponent ds) t)
    (f : principalSeries ℝ (t + 1) (realPositionCharacter ds)) :
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs (additiveJacquetIntegral a f.val) ∈
      RealLocalWhittaker.regularFunctions t (-a)) ∧
    RealUniformWhittaker.HasUniformDerivativeGrowth (additiveJacquetIntegral a f.val) := by
  let L := additiveJacquetForm a hDom
  have hψ (u : G) (hu : u ∈ GeneralLinear.upperUnipotent (t + 1) ℝ)
      (x : principalSeries ℝ (t + 1) (realPositionCharacter ds)) :
      L (translate t ds u x) = realWhittakerCharacter (-a) u * L x := by
    change additiveJacquetIntegral a (fun g => x.val (g * u)) 1 =
      realWhittakerCharacter (-a) u * additiveJacquetIntegral a x.val 1
    rw [additiveJacquetIntegral_rightTranslate, one_mul]
    simpa only [mul_one] using realGodementOpenCellCovariance t a x.val ⟨u, hu⟩ 1
  have h := compactWhittakerSmoothRegularity t ds (-a) L
    (hasCompactDerivativeBound_additiveJacquetForm a hDom) hψ f
  have hValue : (fun g => L (translate t ds g f)) = additiveJacquetIntegral a f.val := by
    funext g
    change additiveJacquetIntegral a (fun k => f.val (k * g)) 1 = additiveJacquetIntegral a f.val g
    rw [additiveJacquetIntegral_rightTranslate, one_mul]
  rw [← hValue]
  exact h

/-- Entire column values for a lower coefficient satisfying the smooth derivative estimates. -/
theorem differentiable_godementLeadingFamily_of_regular (D : RealQuotientMeasureData t) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (hW : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈ RealLocalWhittaker.regularFunctions t (-a))
    (hGrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W) (p : Fin 2) (g : H) :
    Differentiable ℂ (godementLeadingFamily D a Φ W p g) := by
  let g' := weylLong (t + 2) ℝ * g
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  have hI := (realGodementColumnConvergence t D.groupHaar a (rectangularTranslate 1 g' Φ)
    W hW hGrowth p.val).2
  have hM := hI.comp (differentiable_id.add_const ((t : ℂ) / 2))
  let d := determinant g'
  let b : ℂ := (|(d : ℝ)| : ℝ)
  let ε : ℂ := ((((d : ℝ) / |(d : ℝ)| : ℝ) : ℂ)) ^ p.val
  let : NeZero b := ⟨Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr d.ne_zero)⟩
  let s : ℂ := ((t : ℂ) + 1) / 2
  have hOuter (z : ℂ) : determinantWeight (charData p z) s g' = (ε * b ^ z) * b ^ s := by
    change ((charData p z).character d : ℂ) * b ^ s = _
    rw [(charData p z).character_eq]
    rfl
  have hD : Differentiable ℂ (fun z => determinantWeight (charData p z) s g') := by
    rw [funext hOuter]
    exact ((differentiable_const_cpow_of_neZero b).const_mul ε).mul_const (b ^ s)
  exact hD.mul hM

/-- The entire leading-character family agrees with the open-cell Jacquet
integral on the dominant half-plane for all smooth lower position vectors. -/
def RealGodementSmoothLeadingStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock)
    (f : principalSeries ℝ (t + 1) (realPositionCharacter ds)),
    IsStrictlyDominant (realPositionExponent ds) t →
    ∀ (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
      (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
    ∀ (g : Langlands.GeneralLinear (t + 2) ℝ),
      Differentiable ℂ (godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g) ∧
      ∀ z : ℂ, (realPositionExponent ds 0).re < z.re →
        godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g z =
          additiveJacquetIntegral a (sectionValue D.groupHaar (charData p z) f.val Φ) g

theorem realGodementSmoothLeading : RealGodementSmoothLeadingStatement := by
  intro t D a p ds f hDom S hS hRank Φ hΦS g
  obtain ⟨hReg, hGrowth⟩ := regular_additiveJacquetIntegral a hDom f
  refine ⟨differentiable_godementLeadingFamily_of_regular D a Φ _ hReg hGrowth p g, ?_⟩
  intro z hz
  let c := charData p z
  have hUpper : IsStrictlyDominant (realPositionExponent (.character c :: ds)) (t + 1) := by
    intro j hj
    cases j with
    | zero => exact hz
    | succ j => exact hDom j (Nat.lt_of_succ_lt_succ hj)
  have hi := realGodementJointConvergence t D a c ds f.val f.property hUpper S hS hRank Φ hΦS g
  exact (realGodementAdditiveJacquet t D a c f.val Φ g hi).2.2.symm

end Langlands.Global.RankinSelbergGlobal.RealGodement
