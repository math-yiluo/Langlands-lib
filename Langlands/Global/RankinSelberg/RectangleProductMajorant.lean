import Langlands.Global.RankinSelberg.RectangularNormalizedMajorant
import Langlands.Global.RankinSelberg.AdelicSchwartzMellinProduct
import Langlands.Global.RankinSelberg.DualExpansionRectMeasure

/-! # Integrating rectangular product majorants -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

local instance entryMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _
local instance entryBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩
local instance entryT2 : T2Space (Adeles F) := EqualAnalytic.t2Space_adeles F
local instance entryLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F
local instance entrySecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F
local instance entryMatrixLocallyCompact (k m : ℕ) :
    LocallyCompactSpace (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin k → Fin m → Adeles F))
local instance entryMatrixSecondCountable (k m : ℕ) :
    SecondCountableTopology (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin m → Adeles F))

/-- Enumerate the entries of a rectangle as rank-one adelic rows. -/
def rectangleEntryEquiv (d a : ℕ) :
    Matrix (Fin d) (Fin a) (Adeles F) ≃ₜ+ (Fin (d * a) → RowVector F 1) where
  toFun x q _ _ := x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  invFun y i j := y (finProdFinEquiv (i, j)) 0 0
  left_inv x := by ext i j; simp
  right_inv y := by
    funext q i j
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    exact congrArg₂ (y q) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun q => continuous_matrix fun _ _ =>
    continuous_id.matrix_elem _ _
  continuous_invFun := continuous_matrix fun i j =>
    (continuous_apply (finProdFinEquiv (i, j))).matrix_elem 0 0

/-- A product of rank-one Schwartz norms has finite integral for the actual
normalized rectangle measure, including a rectangle with no entries. -/
theorem lintegral_rectangle_prod_enorm_lt_top
    [CompactSpace (AdeleQuotient F)] (d a : ℕ)
    {Ψ : RowVector F 1 → ℂ} (hΨ : Ψ ∈ schwartzBruhat F 1) :
    (∫⁻ x : Matrix (Fin d) (Fin a) (Adeles F),
      ∏ q : Fin (d * a), ‖Ψ (rectangleEntryEquiv F d a x q)‖ₑ
      ∂rectangleMeasure F d a) < ⊤ := by
  let e := rectangleEntryEquiv F d a
  let mu := (rectangleMeasure F d a).map e
  let nu : Measure (Fin (d * a) → RowVector F 1) :=
    Measure.pi fun _ => rectangleMeasure F 1 1
  have hmu : mu.IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map _ e
  have hnu : nu.IsAddHaarMeasure := MeasureTheory.Measure.pi.isAddHaarMeasure _
  have htransport := Measure.isAddLeftInvariant_eq_smul mu nu
  have hscalar := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure mu nu
  obtain ⟨hΨc, hΨi, -⟩ := EqualAnalytic.schwartzBruhat_properties F 1 hΨ
  have hprod : (∫⁻ y : Fin (d * a) → RowVector F 1,
      ∏ q, ‖Ψ (y q)‖ₑ ∂nu) < ⊤ := by
    dsimp [nu]
    rw [AdelicSchwartzMellin.lintegral_fin_prod_eq_prod
      (fun _ : Fin (d * a) => fun y : RowVector F 1 => ‖Ψ y‖ₑ)
      (fun _ => hΨc.measurable.enorm)]
    exact ENNReal.prod_lt_top fun _ _ => hΨi.hasFiniteIntegral
  have hm : (∫⁻ y : Fin (d * a) → RowVector F 1,
      ∏ q, ‖Ψ (y q)‖ₑ ∂mu) < ⊤ := by
    rw [htransport, lintegral_smul_measure]
    exact ENNReal.nnreal_smul_lt_top_iff hscalar.ne' |>.mpr hprod
  erw [← lintegral_map_equiv (fun y : Fin (d * a) → RowVector F 1 =>
    ∏ q, ‖Ψ (y q)‖ₑ) e.toHomeomorph.toMeasurableEquiv]
  exact hm

/-- The joint normalized profile admits one product of rank-one Schwartz
norms in its leading-root and rectangular coordinates. -/
theorem exists_normalized_rectangular_product_majorant
    [CompactSpace (AdeleQuotient F)] (t d : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (Φ : RowVector F (t + 1 + d) → ℂ) (hΦ : Φ ∈ schwartzBruhat F (t + 1 + d)) :
    ∃ Ψ : RowVector F 1 → ℂ, Ψ ∈ schwartzBruhat F 1 ∧
      ∀ (b : Fin (t + 1) → Ideles F)
        (x : Matrix (Fin d) (Fin (t + 1)) (Adeles F))
        (U K : AdelicGL F (t + 1 + d + 1)) (c : Fin (t + 1 + d + 1) → Ideles F),
        PrimitiveAdelicHeight.IsUnitriangular U.val →
        K ∈ PrimitiveAdelicHeight.standardCompact F (t + 1 + d + 1) →
        GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * PrimitiveAdelicHeight.diagonalGL c * K →
          rectangularRootPowerWeight F (t + 1 + d) τ (rectangularCorrectedDiagonal F b c) *
              ‖Φ (gaugeSimpleRootRow F (t + 1 + d) (rectangularCorrectedDiagonal F b c))‖ ≤
            (∏ i : Fin (t + 1), ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b i : Adeles F))‖) *
              ∏ q : Fin (d * (t + 1)), ‖Ψ (rectangleEntryEquiv F d (t + 1) x q)‖ := by
  obtain ⟨Ξ, hΞ, hmajor⟩ := exists_normalized_rectangular_joint_majorant F t d τ hτ Φ hΦ
  obtain ⟨Ψ, hΨ, hprod⟩ := AdelicSchwartzMellin.exists_product_schwartzBruhat_majorant F
    (by omega : 0 < t + 1 + d * (t + 1))
    (EqualAnalytic.schwartzBruhat_properties F _ hΞ).2.2
  refine ⟨Ψ, hΨ, ?_⟩
  intro b x U K c hU hK heq
  refine (hmajor b x U K c hU hK heq).trans ?_
  change _ ≤ (∏ i : Fin (t + 1), ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b i : Adeles F))‖) *
    ∏ q : Fin (d * (t + 1)), ‖Ψ (fun _ _ =>
      x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)‖
  have H := hprod (rectangularJointRow F (gaugeBlockRootIdeles F t b) x)
  rw [Fin.prod_univ_add] at H
  simpa only [rectangularJointRow, Fin.append_left, Fin.append_right] using H

end Langlands.Global.RankinSelbergGlobal
