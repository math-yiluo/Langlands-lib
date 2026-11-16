import Langlands.Global.RankinSelberg.AdelicSchwartzMellin
import Langlands.Global.RankinSelberg.EqualUnfoldingScalar

/-! # Rank-one Mellin convergence for arbitrary idele Haar measures -/

noncomputable section
universe u v w
open NumberField MeasureTheory Langlands Langlands.Global
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace AdelicSchwartzMellin

section HaarTransport

variable {G : Type v} {H : Type w}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  [SecondCountableTopology H]

/-- A continuous group isomorphism transports lower-integral finiteness between
any two Haar normalizations. -/
theorem lintegral_continuousMulEquiv_lt_top_iff
    (e : G ≃ₜ* H) (mu : Measure G) [Measure.IsHaarMeasure mu]
    (nu : Measure H) [Measure.IsHaarMeasure nu] (f : H → ℝ≥0∞) :
    (∫⁻ g, f (e g) ∂mu) < ⊤ ↔ (∫⁻ h, f h ∂nu) < ⊤ := by
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure (mu.map e) nu
  have hm := Measure.isMulLeftInvariant_eq_smul (mu.map e) nu
  erw [← lintegral_map_equiv f e.toHomeomorph.toMeasurableEquiv]
  change (∫⁻ h, f h ∂mu.map e) < ⊤ ↔ _
  rw [hm, lintegral_smul_measure]
  exact ENNReal.nnreal_smul_lt_top_iff hc.ne'

end HaarTransport

local instance mellinHaarSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance mellinHaarSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The actual rank-one adelic points and ideles are continuously isomorphic. -/
def ideleContinuousEquiv : Points F 1 ≃ₜ* Ideles F where
  toFun := ideleOf F
  invFun a := (GeneralLinearGroupPoints.adelicEquiv F 1).symm
    (AdelicGL.scalar F 1 a)
  left_inv z := by
    apply (GeneralLinearGroupPoints.adelicEquiv F 1).injective
    change (GeneralLinearGroupPoints.adelicEquiv F 1)
      ((GeneralLinearGroupPoints.adelicEquiv F 1).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    exact AdelicGL.scalar_determinant_one F _
  right_inv a := by
    change Matrix.GeneralLinearGroup.det
      ((GeneralLinearGroupPoints.adelicEquiv F 1)
        ((GeneralLinearGroupPoints.adelicEquiv F 1).symm
          (Matrix.GeneralLinearGroup.scalar (Fin 1) a))) = a
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    simp
  map_mul' := EqualUnfolding.ideleOf_mul F
  continuous_toFun := EqualUnfolding.continuous_ideleOf F
  continuous_invFun := (GeneralLinearGroupPoints.adelicHomeomorph F 1).symm.continuous.comp
    (AdelicGL.scalar F 1).continuous

/-- The single last-row entry is the underlying adele of the rank-one determinant. -/
theorem lastRow_one_eq (z : Points F 1) :
    lastRow F 0 z = fun _ _ => (ideleOf F z : Adeles F) := by
  ext i j
  simp only [lastRow, Matrix.of_apply, ideleOf,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  exact congrArg₂ (fun i j : Fin 1 =>
    (GeneralLinearGroupPoints.adelicEquiv F 1 z :
      Matrix (Fin 1) (Fin 1) (Adeles F)) i j) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

local instance normalizedIdeleHaar : Measure.IsHaarMeasure (ideleMeasure F) := by
  apply Measure.IsHaarMeasure.smul
  · exact ENNReal.inv_ne_zero.mpr (ideleSlabVolume_ne_top F)
  · exact ENNReal.inv_ne_top.mpr (ideleSlabVolume_ne_zero F)

local instance ideleMellinMeasurableSpace : MeasurableSpace (Ideles F) := borel _

local instance ideleMellinBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩

local instance ideleMellinLocallyCompact : LocallyCompactSpace (Ideles F) :=
  (ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance ideleMellinSecondCountable : SecondCountableTopology (Ideles F) :=
  (ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

/-- Rank-one Mellin convergence on the actual idele group, independently of the
choice of Haar normalization. -/
theorem lintegral_idele_rpow_lt_top
    (mu : Measure (Ideles F)) [Measure.IsHaarMeasure mu]
    {Φ : RowVector F 1 → ℂ} (hΦc : Continuous Φ)
    (hΦ : EqualAnalytic.IsRowDominated F 1 Φ) {σ : ℝ} (hσ : 3 < σ) :
    ∫⁻ a : Ideles F, ‖Φ (fun _ _ => (a : Adeles F))‖ₑ *
      ENNReal.ofReal (((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ) ^ σ) ∂mu < ⊤ := by
  apply (lintegral_continuousMulEquiv_lt_top_iff
    (ideleContinuousEquiv F) (ideleMeasure F) mu _).mp
  change (∫⁻ z, ‖Φ (fun _ _ => (ideleOf F z : Adeles F))‖ₑ *
    ENNReal.ofReal (((IdeleAbsoluteValue.full F (ideleOf F z) : ℝ≥0) : ℝ) ^ σ)
      ∂ideleMeasure F) < ⊤
  simpa only [EqualUnfolding.detNorm_one_eq, lastRow_one_eq] using
    lintegral_lastRow_rpow_lt_top F hΦc hΦ hσ

/-- In particular the rank-one result applies to every Schwartz–Bruhat function. -/
theorem lintegral_idele_schwartzBruhat_rpow_lt_top
    [CompactSpace (AdeleQuotient F)]
    (mu : Measure (Ideles F)) [Measure.IsHaarMeasure mu]
    {Φ : RowVector F 1 → ℂ} (hΦ : Φ ∈ schwartzBruhat F 1)
    {σ : ℝ} (hσ : 3 < σ) :
    ∫⁻ a : Ideles F, ‖Φ (fun _ _ => (a : Adeles F))‖ₑ *
      ENNReal.ofReal (((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ) ^ σ) ∂mu < ⊤ := by
  obtain ⟨hΦc, _, hΦdom⟩ := EqualAnalytic.schwartzBruhat_properties F 1 hΦ
  exact lintegral_idele_rpow_lt_top F mu hΦc hΦdom hσ

end AdelicSchwartzMellin

end Langlands.Global.RankinSelbergGlobal
