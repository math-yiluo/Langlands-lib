import Langlands.Global.RankinSelberg.RealEqualDualConvergence
import Langlands.Global.RankinSelberg.RealGodementAdditiveJacquet
import Langlands.Global.RankinSelberg.RealToralQuotientDensity
import Langlands.Representation.Archimedean.RealLeviShear

/-! # The real Jacquet open cell in lower radical and Levi entry coordinates -/

noncomputable section

open MeasureTheory Langlands.Archimedean
open scoped NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviJacquetChart

open Langlands.GeneralLinear
open ArchimedeanLocal RealGodement RealIwasawa
open Langlands.Whittaker (standardCharacter)
open Langlands.LocalFactor.Archimedean
open RealLeviBorel (vcl vcl_monotone)
open RealLeviChartIntegrable (CoordC lowerC)
open RealLeviTwoBlock (lowerCGL lowerCGL_val)
open RealLeviLeviBorel (CoordM lowerMGL)
open RealLeviShear (shear measurePreserving_shear lowerCGL_shear)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
  borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

private def reverseEntry (n : ℕ) : UpperEntryPair n ≃ CoordC (vcl n) where
  toFun ij := ⟨(ij.val.1.rev, ij.val.2.rev), Fin.lt_def.mp (Fin.rev_lt_rev.mpr ij.property)⟩
  invFun ij := ⟨(ij.val.1.rev, ij.val.2.rev), Fin.rev_lt_rev.mpr (Fin.lt_def.mpr ij.property)⟩
  left_inv ij := Subtype.ext (Prod.ext (Fin.rev_rev ij.val.1) (Fin.rev_rev ij.val.2))
  right_inv ij := Subtype.ext (Prod.ext (Fin.rev_rev ij.val.1) (Fin.rev_rev ij.val.2))

/-- Read strictly lower entries as upper entries by reversing both indices. -/
def upperOfLower (n : ℕ) :
    (CoordC (vcl n) → ℝ) ≃ₜ Langlands.GeneralLinear.upperUnipotent n ℝ :=
  (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (reverseEntry n).symm).trans
    (upperEntryCoordinates (K := ℝ) n).symm

private theorem upperOfLower_entry {n : ℕ} (X : CoordC (vcl n) → ℝ)
    {i j : Fin n} (hij : i < j) :
    (upperOfLower n X).val.val i j = X (reverseEntry n ⟨(i, j), hij⟩) := by
  unfold upperOfLower
  rw [Homeomorph.trans_apply, upperEntryCoordinates_symm_upper _ hij]
  simpa using Homeomorph.piCongrLeft_apply_apply (Y := fun _ => ℝ) (reverseEntry n).symm X
    (reverseEntry n ⟨(i, j), hij⟩)

/-- The Weyl element conjugates the upper chart to the full lower entry chart. -/
theorem weylLong_conj_upperOfLower {n : ℕ} (X : CoordC (vcl n) → ℝ) :
    weylLong n ℝ * (upperOfLower n X).val * weylLong n ℝ = lowerCGL (vcl_monotone n) X := by
  apply Units.ext
  ext i j
  rw [weylLong_conjugate_entry, lowerCGL_val, lowerC, Matrix.of_apply]
  by_cases hij : j < i
  · have hc : vcl n j < vcl n i := Fin.lt_def.mp hij
    rw [dite_eq_left hc, upperOfLower_entry X (Fin.rev_lt_rev.mpr hij)]
    congr 1
    exact Subtype.ext (Prod.ext (Fin.rev_rev i) (Fin.rev_rev j))
  · have hc : ¬ vcl n j < vcl n i := fun h => hij (Fin.lt_def.mpr h)
    rw [dite_eq_right hc]
    rcases eq_or_lt_of_le (le_of_not_gt hij) with rfl | hlt
    · rw [ite_eq_left rfl, UpperUnipotent.entry_diag]
    · rw [ite_eq_right hlt.ne, UpperUnipotent.entry_eq_zero _ (Fin.rev_lt_rev.mpr hlt)]

/-- The scalar factor converting product Lebesgue measure to the specified
self-dual measure in the unipotent entries. -/
def entryScale (n : ℕ) (a : ℝˣ) : ℝ≥0∞ :=
  (NNReal.sqrt ‖(a : ℝ)‖₊ : ℝ≥0∞) ^ Fintype.card (CoordC (vcl n))

private theorem lowerProductMeasure_eq (n : ℕ) (a : ℝˣ) :
    Measure.pi (fun _ : CoordC (vcl n) => (realSelfDualMeasure a).measure) =
      entryScale n a • (volume : Measure (CoordC (vcl n) → ℝ)) := by
  have : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, volume_pi_pi, entryScale, smul_eq_mul]
  change _ = ∏ i, (NNReal.sqrt ‖(a : ℝ)‖₊ : ℝ≥0∞) * volume (s i)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The reverse-entry chart carries the scaled lower Lebesgue measure to the
specified upper Jacquet measure. -/
theorem measurePreserving_upperOfLower (r : ℕ) (a : ℝˣ) :
    MeasurePreserving (upperOfLower (r + 1)) (entryScale (r + 1) a • volume) (upperStepHaar r a) := by
  rw [← lowerProductMeasure_eq]
  have : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : UpperEntryPair (r + 1) => (realSelfDualMeasure a).measure) (reverseEntry (r + 1)).symm
  have h₂ : MeasurePreserving (upperEntryCoordinates (r + 1) (K := ℝ)).symm
      (upperEntryProductMeasure (realSelfDualMeasure a) (r + 1)) (upperStepHaar r a) :=
    ⟨(upperEntryCoordinates (r + 1) (K := ℝ)).symm.continuous.measurable, rfl⟩
  exact h₂.comp h₁

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "w" => weylLong (r + 1) ℝ
local notation "S" => CoordC (vcl (r + 1)) → ℝ

/-- The adjacent lower entry, indexed by the preceding position. -/
def simpleLowerEntry (X : S) (i : Fin r) : ℝ :=
  X ⟨(i.succ, i.castSucc), by change i.val < i.val + 1; omega⟩

theorem standardCharacter_upperOfLower (a : ℝˣ) (X : S) :
    (standardCharacter (realScaledCharacter a) r (upperOfLower n X) : ℂ) =
      (realScaledCharacter a).complex (∑ i, simpleLowerEntry X i) := by
  change (realScaledCharacter a).complex
    (∑ i : Fin r, (upperOfLower n X).val.val i.castSucc i.succ) = _
  congr 1
  calc
    _ = ∑ i : Fin r, simpleLowerEntry X i.rev := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [upperOfLower_entry X Fin.castSucc_lt_succ]
      apply congrArg X
      apply Subtype.ext
      exact Prod.ext (Fin.rev_castSucc i) (Fin.rev_succ i)
    _ = _ := Equiv.sum_comp Fin.revPerm _

/-- In lower coordinates the phase uses the adjacent lower entries, and the Haar
measure contributes the exact scalar `entryScale`. -/
theorem additiveJacquetIntegral_eq_lower (a : ℝˣ) (f : G → ℂ) (g : G) :
    additiveJacquetIntegral a f g = (entryScale n a).toReal *
      ∫ X : S, f (lowerCGL (vcl_monotone n) X * w * g) *
        (realScaledCharacter a).complex (∑ i, simpleLowerEntry X i) := by
  unfold additiveJacquetIntegral
  rw [← (measurePreserving_upperOfLower r a).integral_comp
      (upperOfLower n).toMeasurableEquiv.measurableEmbedding, integral_smul_measure, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with X
  rw [additiveJacquetKernel, standardCharacter_upperOfLower, ← weylLong_conj_upperOfLower,
    mul_assoc (w * (upperOfLower n X).val) w w, weylLong_mul_self, mul_one]

/-- The weight on a simple lower entry after moving the logarithmic diagonal
through the original upper unipotent. -/
def lowerTorusFrequency (y : Fin (r + 1) → ℝ) (i : Fin r) : ℝ :=
  Real.exp (y i.succ.rev - y i.castSucc.rev)

private theorem conjTorus_entry (y : Fin (r + 1) → ℝ)
    (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (i j : Fin (r + 1)) :
    (conjTorus y u).val.val i j = Real.exp (y i - y j) * u.val.val i j := by
  change ((torus y * u.val * torus (-y)).val) i j = _
  rw [Units.val_mul, Units.val_mul, torus_val, torus_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.neg_apply, sub_eq_add_neg, Real.exp_add]
  ring

private theorem standardCharacter_conjTorus_upperOfLower (a : ℝˣ)
    (y : Fin (r + 1) → ℝ) (X : S) :
    (standardCharacter (realScaledCharacter a) r (conjTorus y (upperOfLower n X)) : ℂ) =
      (realScaledCharacter a).complex (∑ i, lowerTorusFrequency y i * simpleLowerEntry X i) := by
  rw [Langlands.Whittaker.standardCharacter_apply]
  congr 1
  calc
    _ = ∑ i : Fin r, lowerTorusFrequency y i.rev * simpleLowerEntry X i.rev := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [conjTorus_entry, upperOfLower_entry X Fin.castSucc_lt_succ]
      have hfreq : lowerTorusFrequency y i.rev = Real.exp (y i.castSucc - y i.succ) := by
        simp only [lowerTorusFrequency, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev]
      rw [hfreq]
      congr 1
      apply congrArg X
      exact Subtype.ext (Prod.ext (Fin.rev_castSucc i) (Fin.rev_succ i))
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i => lowerTorusFrequency y i * simpleLowerEntry X i)

private theorem weylLong_conjTorus_mul (y : Fin (r + 1) → ℝ)
    (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (k : G) :
    w * (conjTorus y u).val * (torus y * k) =
      torus (fun i => y i.rev) * (w * u.val * w) * w * k := by
  change w * (torus y * u.val * torus (-y)) * (torus y * k) = _
  rw [torus_neg, ← RealEqualDualConvergence.weylLong_torus_weylLong]
  calc
    _ = w * torus y * u.val * k := by group
    _ = w * torus y * (w * w) * u.val * (w * w) * k := by simp
    _ = _ := by group

private theorem kernel_conjTorus_upperOfLower (a : ℝˣ) (f : G → ℂ)
    (y : Fin (r + 1) → ℝ) (k : G) (X : S) :
    additiveJacquetKernel a f (torus y * k) (conjTorus y (upperOfLower n X)) =
      f (torus (fun i => y i.rev) * lowerCGL (vcl_monotone n) X * w * k) *
        (realScaledCharacter a).complex (∑ i, lowerTorusFrequency y i * simpleLowerEntry X i) := by
  rw [additiveJacquetKernel, weylLong_conjTorus_mul, weylLong_conj_upperOfLower,
    standardCharacter_conjTorus_upperOfLower]

/-- Moving the positive torus across the cell and reversing the entries multiplies
the measure by the upper-unipotent modulus and reweights each simple frequency. -/
theorem additiveJacquetIntegral_eq_lowerTorus (a : ℝˣ) (f : G → ℂ)
    (y : Fin (r + 1) → ℝ) (k : G)
    (hI : Integrable (additiveJacquetKernel a f (torus y * k)) (upperStepHaar r a)) :
    Integrable (fun X : S => f (torus (fun i => y i.rev) * lowerCGL (vcl_monotone n) X * w * k) *
          (realScaledCharacter a).complex (∑ i, lowerTorusFrequency y i * simpleLowerEntry X i)) ∧
    additiveJacquetIntegral a f (torus y * k) =
      ((Real.exp (torusModularLog n y) * (entryScale n a).toReal : ℝ) : ℂ) *
        ∫ X : S, f (torus (fun i => y i.rev) * lowerCGL (vcl_monotone n) X * w * k) *
          (realScaledCharacter a).complex (∑ i, lowerTorusFrequency y i * simpleLowerEntry X i) := by
  let K := additiveJacquetKernel a f (torus y * k)
  let μ := upperStepHaar r a
  let e := (conjTorusHomeomorph (-y)).toMeasurableEquiv
  have : μ.IsHaarMeasure := upperStepHaar_isHaar r a
  have he : MeasurePreserving e μ (ENNReal.ofReal (Real.exp (torusModularLog n y)) • μ) := by
    refine ⟨e.measurable, ?_⟩
    change μ.map (conjTorus (-y)) = _
    rw [map_conjTorus, map_neg, neg_neg]
  have hk (X : S) :
      K (e.symm (upperOfLower n X)) =
        f (torus (fun i => y i.rev) * lowerCGL (vcl_monotone n) X * w * k) *
          (realScaledCharacter a).complex (∑ i, lowerTorusFrequency y i * simpleLowerEntry X i) := by
    have he' (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) :
        e.symm u = conjTorus y u := by
      change conjTorus (-(-y)) u = _
      rw [neg_neg]
    rw [he']
    exact kernel_conjTorus_upperOfLower a f y k X
  have hscaled : Integrable (fun u => K (e.symm u))
      (ENNReal.ofReal (Real.exp (torusModularLog n y)) • μ) :=
    (he.symm e).integrable_comp_of_integrable hI
  have hunscaled : Integrable (fun u => K (e.symm u)) μ :=
    (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
      ENNReal.ofReal_ne_top).mp hscaled
  have hscale (a : ℝˣ) :
      entryScale n a ≠ 0 ∧ entryScale n a ≠ ⊤ := by
    rw [entryScale, ← ENNReal.coe_pow]
    exact ⟨ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)).ne'),
      ENNReal.coe_ne_top⟩
  have hLower := (measurePreserving_upperOfLower r a).integrable_comp_of_integrable hunscaled
  refine ⟨((integrable_smul_measure (hscale a).1 (hscale a).2).mp hLower).congr
    (ae_of_all _ hk), ?_⟩
  have hchange := he.integral_comp e.measurableEmbedding (fun u => K (e.symm u))
  simp only [MeasurableEquiv.symm_apply_apply] at hchange
  change (∫ u, K u ∂μ) = _
  rw [hchange, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  rw [← (measurePreserving_upperOfLower r a).integral_comp
      (upperOfLower n).toMeasurableEquiv.measurableEmbedding (fun u => K (e.symm u)),
    integral_smul_measure, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  congr 1
  congr 1
  exact integral_congr_ae (ae_of_all _ hk)

section LeviSplit

open RealLeviLeviBorel (lowerM lowerM_isLowerTriangular)
open RealLeviShear (toCoordS embedS_inl embedS_inr shearL_apply lowerM_self strictC)

variable {ι : Type*} [LinearOrder ι] {cl : Fin (r + 1) → ι}

/-- An adjacent lower entry belongs to the radical at a class boundary and to the
Levi inside a class. -/
def leviSimpleEntry (hcl : Monotone cl) (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ)
    (i : Fin r) : ℝ :=
  if h : cl i.castSucc < cl i.succ then X ⟨(i.succ, i.castSucc), h⟩
  else Z ⟨(i.succ, i.castSucc),
    (le_antisymm (not_lt.mp h) (hcl Fin.castSucc_lt_succ.le)), Fin.castSucc_lt_succ⟩

theorem simpleLowerEntry_shear (hcl : Monotone cl) (Z : CoordM cl → ℝ)
    (X : CoordC cl → ℝ) (i : Fin r) :
    simpleLowerEntry (shear hcl (Z, X)) i = leviSimpleEntry hcl Z X i := by
  by_cases hi : cl i.castSucc < cl i.succ
  · have hcoord : (⟨(i.succ, i.castSucc), Fin.lt_def.mp Fin.castSucc_lt_succ⟩ :
        CoordC (vcl (r + 1))) = toCoordS hcl (.inr ⟨(i.succ, i.castSucc), hi⟩) := rfl
    unfold simpleLowerEntry leviSimpleEntry
    rw [dite_eq_left hi, hcoord, shear, embedS_inr, shearL_apply, Matrix.mul_apply]
    simp only
    rw [Finset.sum_eq_single i.succ]
    · rw [lowerM_self, strictC, Matrix.of_apply, dite_eq_left hi, one_mul]
    · intro j _ hj
      by_cases hjk : i.succ < j
      · have hz : lowerM cl Z i.succ j = 0 := lowerM_isLowerTriangular cl Z hjk
        rw [hz, zero_mul]
      have hj' : j ≤ i.castSucc := by
        have h₀ := Fin.le_def.mp (le_of_not_gt hjk)
        have h₁ := Fin.val_ne_of_ne hj
        exact Fin.le_def.mpr (by
          simp only [Fin.val_succ] at h₀ h₁
          simp only [Fin.val_castSucc]
          omega)
      rw [strictC, Matrix.of_apply, dite_eq_right (not_lt_of_ge (hcl hj')), mul_zero]
    · simp
  · let h : cl i.succ = cl i.castSucc := le_antisymm (not_lt.mp hi) (hcl Fin.castSucc_lt_succ.le)
    have hcoord : (⟨(i.succ, i.castSucc), Fin.lt_def.mp Fin.castSucc_lt_succ⟩ :
        CoordC (vcl (r + 1))) = toCoordS hcl (.inl ⟨(i.succ, i.castSucc), h, Fin.castSucc_lt_succ⟩) := rfl
    unfold simpleLowerEntry leviSimpleEntry
    rw [dite_eq_right hi, hcoord, shear, embedS_inl]

/-- Lebesgue integration on the full lower chart can be done by first integrating
in the Levi lower entries and then in the opposite radical entries. The phase
allows a separate frequency on every adjacent lower entry. -/
def RealLeviJacquetChartStatement : Prop :=
  ∀ (r : ℕ) (cl : Fin (r + 1) → ℕ) (hcl : Monotone cl) (F : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (s : Fin r → ℝ) (a : ℝˣ),
    Integrable (fun X : CoordC (vcl (r + 1)) → ℝ =>
      F (lowerCGL (vcl_monotone (r + 1)) X) *
        (realScaledCharacter a).complex (∑ i, s i * simpleLowerEntry X i)) →
    (∫ X : CoordC (vcl (r + 1)) → ℝ,
      F (lowerCGL (vcl_monotone (r + 1)) X) *
        (realScaledCharacter a).complex (∑ i, s i * simpleLowerEntry X i)) =
      ∫ X : CoordC cl → ℝ, ∫ Z : CoordM cl → ℝ,
        F (lowerMGL cl Z * lowerCGL hcl X) *
          (realScaledCharacter a).complex (∑ i, s i * leviSimpleEntry hcl Z X i)

theorem realLeviJacquetChart : RealLeviJacquetChartStatement := by
  intro r cl hcl F s a hI
  let K (X : CoordC (vcl (r + 1)) → ℝ) :=
    F (lowerCGL (vcl_monotone (r + 1)) X) *
      (realScaledCharacter a).complex (∑ i, s i * simpleLowerEntry X i)
  have hI' : Integrable K := hI
  let e := shear hcl
  have he : MeasurePreserving e (volume.prod volume) volume := measurePreserving_shear hcl
  have hIe : Integrable (fun p => K (e p)) (volume.prod volume) :=
    he.integrable_comp_of_integrable hI'
  change (∫ X, K X) = _
  calc
    _ = ∫ p, K (e p) ∂(volume.prod volume) := by
      rw [← integral_map he.measurable.aemeasurable (he.map_eq.symm ▸ hI'.aestronglyMeasurable),
        he.map_eq]
    _ = _ := by
      rw [integral_prod_symm _ hIe]
      simp only [K, e, lowerCGL_shear, simpleLowerEntry_shear]

/-- In the absolutely convergent Jacquet integral at a torus translate, move the
torus through the cell and integrate first in the Levi coordinates. -/
theorem additiveJacquetIntegral_eq_levi {cl : Fin (r + 1) → ℕ} (hcl : Monotone cl)
    (a : ℝˣ) (f : G → ℂ) (y : Fin (r + 1) → ℝ) (k : G)
    (hI : Integrable (additiveJacquetKernel a f (torus y * k)) (upperStepHaar r a)) :
    additiveJacquetIntegral a f (torus y * k) =
      ((Real.exp (torusModularLog n y) * (entryScale n a).toReal : ℝ) : ℂ) *
        ∫ X : CoordC cl → ℝ, ∫ Z : CoordM cl → ℝ,
          f (torus (fun i => y i.rev) * (lowerMGL cl Z * lowerCGL hcl X) * w * k) *
            (realScaledCharacter a).complex (∑ i, lowerTorusFrequency y i * leviSimpleEntry hcl Z X i) := by
  obtain ⟨hK, hEq⟩ := additiveJacquetIntegral_eq_lowerTorus a f y k hI
  rw [hEq, realLeviJacquetChart r cl hcl (fun g => f (torus (fun i => y i.rev) * g * w * k))
    (lowerTorusFrequency y) a hK]

end LeviSplit

end Langlands.Global.RankinSelbergGlobal.RealLeviJacquetChart
