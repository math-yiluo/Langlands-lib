import Langlands.Global.RankinSelberg.ComplexLocalEqualRecursionComparison
import Langlands.Global.RankinSelberg.ComplexLocalEqualUnfoldingFubini
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerDual
import Langlands.Representation.GodementJacquet.ComplexTriangularMatchedTests

/-! # Paired equal-rank unfolding for the quotient recursion and its dual -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexCharacterChange (model_unipotent_mul model_mul_scalar coe_centralCharacter
  whittakerCharacter_neg_parameter)
open ComplexLocalWhittakerDual (dualData dualFunction_mem length_dualData)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => GeneralLinear.upperUnipotent m ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n

private theorem whittakerCharacter_equalPad (a : ℂˣ) (u : N) :
    complexWhittakerCharacter a (pad u.val) = complexWhittakerCharacter a u.val := by
  apply congrArg (fun z : ℂ => (complexScaledCharacter a).complex z)
  rw [Fin.sum_univ_castSucc]
  have hlast : (pad u.val).val (Fin.last r).castSucc (Fin.last r).succ = 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (by simp)]
    exact Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ)
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨Nat.lt_succ_of_lt i.isLt, Nat.succ_lt_succ i.isLt⟩]
  rfl

private theorem equalPair_unipotent_mul {a : ℂˣ} {ds es : List ComplexCharacterData}
    {U : H → ℂ} {V : G → ℂ} (hU : U ∈ complexWhittakerModel r ds a)
    (hV : V ∈ complexWhittakerModel (r + 1) es (-a)) (g : G) (u : N) (h : H) :
    U (u.val * h) * V (pad (u.val * h) * g) = U h * V (pad h * g) := by
  rw [model_unipotent_mul hU u, map_mul, mul_assoc (pad u.val),
    complexWhittakerModel_left_equivariant hV _ (complexEqualPad_mem_upperUnipotent u),
    whittakerCharacter_equalPad, mul_mul_mul_comm, whittakerCharacter_neg_parameter, one_mul]

private theorem inverseCharacter_at_neg_one (d : ComplexCharacterData) :
    d.inv.character (-1) = d.character (-1) := by
  change (d.character (-1))⁻¹ = _
  rw [← map_inv]
  simp

private theorem dualData_centralSign (ds : List ComplexCharacterData) :
    complexCentralSign (dualData ds) = complexCentralSign ds := by
  simp [dualData, complexCentralSign, List.map_map, List.map_reverse, List.prod_reverse,
    Function.comp_def, inverseCharacter_at_neg_one]

/-- A pointwise scalar relation in the first coefficient passes to the equal-rank integral. -/
theorem complexEqualIntegral_scale_left_of_eq (D : ComplexQuotientMeasureData (r + 1))
    (c : ℂ) (W W₀ V : G → ℂ) (φ : Row → ℂ) (s : ℂ) (h : ∀ g, c * W g = W₀ g) :
    c * complexEqualIntegral D W V φ s = complexEqualIntegral D W₀ V φ s := by
  unfold complexEqualIntegral ArchimedeanLocal.equalIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  dsimp only [ArchimedeanLocal.equalIntegrand]
  rw [← h]
  ring

/-- On the dual Whittaker functions, the mixed square transform incurs the
central sign of the smaller inducing list. -/
theorem complexEqualUnfoldedSign_of_mem (D : ComplexQuotientMeasureData (r + 1))
    (D₁ : ComplexQuotientMeasureData r) (η : ℂˣ →* ℂˣ) (a : ℂˣ)
    (ds es : List ComplexCharacterData) (hds : ds.length = m) (hes : es.length = n)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (Φ : Rect → ℂ) (φ : Row → ℂ) (s : ℂ) :
    (η (-1) : ℂ) ^ m * complexEqualUnfoldedIntegral D.groupHaar D₁ η
      (complexSquareProductTest (complexRectangularFourier (-a) Φ) (complexFourierTransform a φ))
      (ud U.val) (wd V.val) s =
    complexCentralSign ds * complexEqualUnfoldedIntegral D.groupHaar D₁ η
      (complexMatrixFourier a (complexSquareProductTest Φ φ)) (ud U.val) (wd V.val) s := by
  have hU := dualFunction_mem hds U.2
  have hV := dualFunction_mem hes V.2
  refine complexLocalEqualUnfoldedSign (r := r) D.groupHaar D.groupHaar_isHaar D₁ η a Φ φ
    (ud U.val) (wd V.val) (complexCentralSign ds) (equalPair_unipotent_mul hU hV) ?_ s
  intro h
  rw [model_mul_scalar ((length_dualData ds).trans hds) hU, coe_centralCharacter,
    ← complexCentralSign, dualData_centralSign]

/-- With one positive Haar scalar, the rectangular recursion and its dual
give the equal-rank unfolded integrals when their respective product kernels
are continuous and integrable. -/
def ComplexLocalEqualPairedUnfoldingStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ),
  ∃ c : ℝ≥0, 0 < c ∧
  ∀ (d : ComplexCharacterData) (ds es : List ComplexCharacterData), ds.length = m → es.length = n →
  ∀ (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (Φ : SchwartzMap Rect ℂ) (φ : Row → ℂ) (s : ℂ),
    let W := complexJacquetRecursion a D₁ Φ U.val d.character
    let A := complexEqualUnfoldingProductKernel d.character Φ φ U.val V.val s
    let Ad := complexEqualUnfoldingProductKernel d.inv.character (complexRectangularFourier (-a) Φ)
      (complexFourierTransform a φ) (ud U.val) (wd V.val) s
    (Continuous A → Integrable A (D₁.measure.prod D.groupHaar) →
      (c : ℂ) * complexEqualIntegral D W V.val φ s =
        complexEqualUnfoldedIntegral D.groupHaar D₁ d.character (complexSquareProductTest Φ φ)
          U.val V.val s) ∧
    (Continuous Ad → Integrable Ad (D₁.measure.prod D.groupHaar) →
      (c : ℂ) * complexEqualDualIntegral a D W V.val φ s =
        complexCentralSign ds * complexEqualUnfoldedIntegral D.groupHaar D₁ d.inv.character
          (complexMatrixFourier a (complexSquareProductTest Φ φ)) (ud U.val) (wd V.val) s)

set_option maxHeartbeats 1600000 in
theorem complexLocalEqualPairedUnfolding : ComplexLocalEqualPairedUnfoldingStatement (r := r) := by
  intro D D₁ a
  obtain ⟨c, hc, hrec⟩ := complexLocalEqualRecursionComparison (r := r) D D₁ a
  refine ⟨c, hc, ?_⟩
  intro d ds es hds hes U V Φ φ s W A Ad
  have hV (u : GeneralLinear.upperUnipotent n ℂ) (g : G) :
      V.val (u.val * g) = complexWhittakerCharacter (-a) u.val * V.val g :=
    model_unipotent_mul V.2 u g
  constructor
  · intro hAc hAi
    let R := complexEqualUnipotentRecursion D D₁ d.character a Φ U.val
    calc
      _ = complexEqualIntegral D R V.val φ s :=
        complexEqualIntegral_scale_left_of_eq D c W R V.val φ s
          (fun g => (hrec a rfl d.character Φ U.val g).symm)
      _ = _ := complexLocalEqualUnfoldingFubini D D₁ d.character a Φ φ R V.val U.val
        (fun _ => rfl) hV s hAc hAi
  · intro hAdc hAdi
    let Φd := complexRectangularFourier (-a) Φ
    let φd := complexFourierTransform a φ
    let Ud := ud U.val
    let Vd := wd V.val
    let Rd := complexEqualUnipotentRecursion D D₁ d.inv.character (-a) Φd Ud
    let b : ℂ := (d.character (-1) : ℂ) ^ m
    obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexRectangularFourier (-a) Φ
    have hΨ' : (Ψ : Rect → ℂ) = Φd := hΨ
    have hη : (d.inv.character : ℂˣ →* ℂˣ) = (d.character : ℂˣ →* ℂˣ).comp invMonoidHom := by
      apply MonoidHom.ext
      intro z
      change (d.character z)⁻¹ = d.character z⁻¹
      exact (map_inv d.character z).symm
    have hRaw (g : G) : (c : ℂ) * wd W g = b * Rd g := by
      have hd := complexJacquetRecursion_dual a D₁ Φ U.val d.character
        (fun u k => model_unipotent_mul U.2 u k) g
      change wd W g = b * complexJacquetRecursion (-a) D₁ Φd Ud
        ((d.character : ℂˣ →* ℂˣ).comp invMonoidHom) g at hd
      rw [← hη] at hd
      have hRd : Rd g = (c : ℂ) * complexJacquetRecursion (-a) D₁ Φd Ud d.inv.character g := by
        simpa only [hΨ'] using
          hrec (-a) (complexSelfDualMeasure_neg_scale a) d.inv.character Ψ Ud g
      rw [hd, hRd]
      ring
    have hVd : Vd ∈ complexWhittakerModel (r + 1) (dualData es) (-(-a)) :=
      dualFunction_mem hes V.2
    have hb : b = (d.inv.character (-1) : ℂ) ^ m := by
      rw [inverseCharacter_at_neg_one]
    calc
      _ = complexEqualIntegral D (fun g => b * Rd g) Vd φd s :=
        complexEqualIntegral_scale_left_of_eq D c (wd W) _ Vd φd s hRaw
      _ = b * complexEqualIntegral D Rd Vd φd s :=
        (complexEqualIntegral_scale_left_of_eq D b Rd _ Vd φd s (fun _ => rfl)).symm
      _ = b * complexEqualUnfoldedIntegral D.groupHaar D₁ d.inv.character
          (complexSquareProductTest Φd φd) Ud Vd s := by
        rw [complexLocalEqualUnfoldingFubini D D₁ d.inv.character (-a) Φd φd Rd Vd Ud
          (fun _ => rfl) (model_unipotent_mul hVd) s hAdc hAdi]
      _ = _ := by
        rw [hb]
        exact complexEqualUnfoldedSign_of_mem D D₁ d.inv.character a ds es hds hes U V Φ φ s

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
