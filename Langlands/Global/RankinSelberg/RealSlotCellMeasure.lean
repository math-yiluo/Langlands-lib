import Langlands.Global.RankinSelberg.RealSlotOpenCell

/-! # The upper entry Haar measure in Levi coordinates of the open cell -/

noncomputable section

open MeasureTheory Matrix
open scoped NNReal ENNReal
open Langlands.Archimedean
open Langlands.Archimedean.RealLeviChartIntegrable Langlands.Archimedean.RealLeviTwoBlock
open Langlands.Archimedean.RealLeviBorel Langlands.Archimedean.RealLeviLeviBorel
open Langlands.Archimedean.RealLeviShear
open Langlands.Global.RankinSelbergGlobal.RealGodement (upperStepHaar)

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

private local instance (d : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent d ℝ) :=
  borel _
private local instance (d : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent d ℝ) := ⟨rfl⟩

variable {r : ℕ}

/-! ## Upper entries from lower coordinates -/

/-- The upper entry `(i, j)` corresponds to the lower coordinate `(rev i, rev j)`. -/
def revPair : Langlands.GeneralLinear.UpperEntryPair (r + 1) ≃ CoordC (vcl (r + 1)) where
  toFun ij := ⟨(ij.1.1.rev, ij.1.2.rev), by
    change (ij.1.2.rev : ℕ) < ij.1.1.rev
    exact Fin.rev_lt_rev.mpr ij.2⟩
  invFun x := ⟨(x.1.1.rev, x.1.2.rev), Fin.rev_lt_rev.mpr x.2⟩
  left_inv _ := by simp
  right_inv x := by simp

/-- The upper unipotent matrix whose entry `(i, j)` is the lower coordinate `(rev i, rev j)`. -/
def upperOfLower (Y : CoordC (vcl (r + 1)) → ℝ) : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ :=
  (Langlands.GeneralLinear.upperEntryCoordinates (r + 1)).symm fun ij => Y (revPair ij)

theorem continuous_upperOfLower : Continuous (upperOfLower (r := r)) :=
  (Langlands.GeneralLinear.upperEntryCoordinates (r + 1)).symm.continuous.comp
    (continuous_pi fun _ => continuous_apply _)

/-- **The long Weyl element turns lower coordinates into upper ones**:
`w · u(Y) = n̄_B(Y) · w`. -/
theorem weylLong_mul_upperOfLower (Y : CoordC (vcl (r + 1)) → ℝ) :
    Langlands.GeneralLinear.weylLong (r + 1) ℝ *
        ((upperOfLower Y : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) :
          Langlands.GeneralLinear (r + 1) ℝ) =
      lowerCGL (vcl_monotone (r + 1)) Y * Langlands.GeneralLinear.weylLong (r + 1) ℝ := by
  apply Units.ext
  ext i j
  rw [Langlands.GeneralLinear.weylLong_mul_entry, Langlands.GeneralLinear.mul_weylLong_entry]
  change (upperOfLower Y).val.val i.rev j = lowerC (vcl (r + 1)) Y i j.rev
  rcases lt_trichotomy i.rev j with h | h | h
  · rw [upperOfLower, Langlands.GeneralLinear.upperEntryCoordinates_symm_upper _ h]
    have hc : vcl (r + 1) j.rev < vcl (r + 1) i := by
      change (j.rev : ℕ) < i
      have := Fin.rev_lt_rev.mpr h
      rw [Fin.rev_rev] at this
      exact this
    simp only [lowerC, of_apply, dite_eq_left hc]
    congr 1
    apply Subtype.ext
    simp [revPair]
  · subst h
    rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag]
    have hc : ¬ vcl (r + 1) i.rev.rev < vcl (r + 1) i := by simp [vcl]
    simp [lowerC]
  · rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero _ h]
    have h' : i < j.rev := by
      have := Fin.rev_lt_rev.mpr h
      rwa [Fin.rev_rev] at this
    have hc : ¬ vcl (r + 1) j.rev < vcl (r + 1) i := by
      change ¬ (j.rev : ℕ) < i
      exact not_lt.mpr (Fin.le_def.mp h'.le)
    simp [lowerC, hc, h'.ne]

/-! ## The Haar measure -/

theorem pi_smul_volume {ι : Type*} [Fintype ι] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • (volume : Measure ℝ)) =
      (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => (volume : Measure ℝ)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  push_cast
  ring

/-- The constant relating the self-dual upper entry measure to Lebesgue measure. -/
def haarScale (r : ℕ) (a : ℝˣ) : ℝ≥0 :=
  NNReal.sqrt ‖(a : ℝ)‖₊ ^ Fintype.card (Langlands.GeneralLinear.UpperEntryPair (r + 1))

theorem haarScale_pos (r : ℕ) (a : ℝˣ) : 0 < haarScale r a :=
  pow_pos (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) _

theorem upperStepHaar_eq (a : ℝˣ) :
    upperStepHaar r a = haarScale r a • Measure.map (upperOfLower (r := r)) volume := by
  have hpi := measurePreserving_piCongrLeft
    (fun _ : Langlands.GeneralLinear.UpperEntryPair (r + 1) => (volume : Measure ℝ))
    (revPair (r := r)).symm
  have he : (Langlands.GeneralLinear.upperEntryCoordinates (r + 1) (K := ℝ)).symm ∘
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (revPair (r := r)).symm) =
        upperOfLower (r := r) := by
    funext Y
    simp only [Function.comp_apply, upperOfLower]
    congr 1
    funext ij
    obtain ⟨x, rfl⟩ := (revPair (r := r)).symm.surjective ij
    change Equiv.piCongrLeft (fun _ => ℝ) revPair.symm Y (revPair.symm x) = _
    rw [Equiv.piCongrLeft_apply_apply]
    simp
  change (Measure.pi fun _ => (Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal.realSelfDualMeasure
    a).measure).map _ = _
  rw [show (Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal.realSelfDualMeasure a).measure =
      NNReal.sqrt ‖(a : ℝ)‖₊ • volume from rfl, pi_smul_volume,
    Measure.map_smul _
      (Langlands.GeneralLinear.upperEntryCoordinates (r + 1) (K := ℝ)).symm.continuous.measurable.aemeasurable,
    ← hpi.map_eq, Measure.map_map
      (Langlands.GeneralLinear.upperEntryCoordinates (r + 1) (K := ℝ)).symm.continuous.measurable
      (MeasurableEquiv.measurable _), he]
  rfl

/-! ## Fubini in the Levi coordinates -/

section Fubini

variable {ι : Type*} [LinearOrder ι] {cl : Fin (r + 1) → ι} (hcl : Monotone cl)

/-- The point of the open cell with Levi coordinates `Z` and opposite radical coordinates `X`. -/
def cellPt (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) :
    Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ :=
  upperOfLower (shear hcl (Z, X))

theorem weylLong_mul_cellPt (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) :
    Langlands.GeneralLinear.weylLong (r + 1) ℝ *
        ((cellPt hcl Z X : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) :
          Langlands.GeneralLinear (r + 1) ℝ) =
      lowerMGL cl Z * lowerCGL hcl X * Langlands.GeneralLinear.weylLong (r + 1) ℝ := by
  rw [cellPt, weylLong_mul_upperOfLower, lowerCGL_shear]

theorem lowerCGL_zero : lowerCGL hcl (0 : CoordC cl → ℝ) = 1 := by
  apply Units.ext
  rw [lowerCGL_val, Units.val_one]
  ext p q
  simp only [lowerC, of_apply, Pi.zero_apply]
  split_ifs with h h'
  · rw [Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  · rw [h', Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h']

theorem lowerMGL_zero : lowerMGL cl (0 : CoordM cl → ℝ) = 1 := by
  apply Units.ext
  rw [lowerMGL_val, Units.val_one]
  ext p q
  simp only [lowerM, of_apply, Pi.zero_apply]
  split_ifs with h h'
  · rw [Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h.2
  · rw [h', Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h']

/-- The open cell point factors into its block part and its opposite radical part. -/
theorem cellPt_mul (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) :
    cellPt hcl Z X = cellPt hcl Z 0 * cellPt hcl 0 X := by
  apply Subtype.ext
  apply mul_left_cancel (a := Langlands.GeneralLinear.weylLong (r + 1) ℝ)
  rw [Subgroup.coe_mul, ← mul_assoc, weylLong_mul_cellPt, weylLong_mul_cellPt, lowerCGL_zero,
    mul_one]
  have h0 := weylLong_mul_cellPt hcl 0 X
  rw [lowerMGL_zero, one_mul] at h0
  rw [mul_assoc (lowerMGL cl Z) (Langlands.GeneralLinear.weylLong (r + 1) ℝ), h0, mul_assoc]

/-- **Fubini in the Levi coordinates of the open cell.** For a continuous function on the upper
unipotent group that is integrable for the self-dual entry measure, its composition with the open
cell point is integrable for the product of the Lebesgue measures, and its integral is
`haarScale r a` times the iterated integral over the opposite radical coordinates `X` of the
integral over the block coordinates `Z`. -/
theorem integral_upperStepHaar_eq (a : ℝˣ)
    {F : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ → ℂ} (hF : Continuous F)
    (hI : Integrable F (upperStepHaar r a)) :
    Integrable (fun p : (CoordM cl → ℝ) × (CoordC cl → ℝ) => F (cellPt hcl p.1 p.2))
        (volume.prod volume) ∧
      ∫ u, F u ∂upperStepHaar r a =
        (haarScale r a : ℝ) * ∫ X, ∫ Z, F (cellPt hcl Z X) := by
  set ν := Measure.map (upperOfLower (r := r)) volume
  have hmp : MeasurePreserving (fun p : (CoordM cl → ℝ) × (CoordC cl → ℝ) => cellPt hcl p.1 p.2)
      (volume.prod volume) ν :=
    (⟨continuous_upperOfLower.measurable, rfl⟩ : MeasurePreserving (upperOfLower (r := r))
      volume ν).comp (measurePreserving_shear hcl)
  have hIν : Integrable F ν := by
    rw [upperStepHaar_eq, ← Measure.coe_nnreal_smul] at hI
    exact (integrable_smul_measure (by simpa using (haarScale_pos r a).ne')
      ENNReal.coe_ne_top).mp hI
  have hcomp : Integrable (fun p : (CoordM cl → ℝ) × (CoordC cl → ℝ) => F (cellPt hcl p.1 p.2))
      (volume.prod volume) :=
    (hmp.integrable_comp hF.aestronglyMeasurable).mpr hIν
  refine ⟨hcomp, ?_⟩
  rw [upperStepHaar_eq, integral_smul_nnreal_measure]
  change (haarScale r a) • ∫ x, F x ∂ν = _
  rw [← hmp.map_eq,
    integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable),
    integral_prod_symm _ hcomp, NNReal.smul_def, Complex.real_smul]

end Fubini

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
