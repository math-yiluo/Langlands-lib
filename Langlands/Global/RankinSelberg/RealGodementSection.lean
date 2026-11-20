import Langlands.Global.RankinSelberg.RealGodementSmooth
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Group.Integral

/-! # The real Godement section for the upper triangular Borel -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

private def absPower (z : ℂ) : ℝˣ →* ℂ where
  toFun x := ((|(x : ℝ)| : ℝ) : ℂ) ^ z
  map_one' := by simp
  map_mul' x y := by
    change ((|(x : ℝ) * (y : ℝ)| : ℝ) : ℂ) ^ z = _
    rw [abs_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _) z]

@[simp] private theorem absPower_apply (z : ℂ) (x : ℝˣ) :
    absPower z x = ((|(x : ℝ)| : ℝ) : ℂ) ^ z := rfl

private def scalarWeight (c : RealCharacterData) (z : ℂ) : ℝˣ →* ℂ where
  toFun x := (c.character x : ℂ) * absPower z x
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Units.val_mul]; ring

/-- The real inducing character of the determinant with its absolute-value shift. -/
def determinantWeight {n : ℕ} (c : RealCharacterData) (z : ℂ) :
    Langlands.GeneralLinear n ℝ →* ℂ :=
  (scalarWeight c z).comp Matrix.GeneralLinearGroup.det

private theorem absPower_base_ne_zero (x : ℝˣ) :
    ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast abs_ne_zero.mpr x.ne_zero

private theorem determinantWeight_ne_zero {n : ℕ} (c : RealCharacterData) (z : ℂ)
    (g : Langlands.GeneralLinear n ℝ) : determinantWeight c z g ≠ 0 :=
  mul_ne_zero (c.character (Matrix.GeneralLinearGroup.det g)).ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (absPower_base_ne_zero _)))

private theorem determinantWeight_add_shift {n : ℕ} (c : RealCharacterData) (z w : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    absPower w (Matrix.GeneralLinearGroup.det g) * determinantWeight c z g =
      determinantWeight c (z + w) g := by
  change _ * ((c.character _ : ℂ) * absPower z _) =
    (c.character _ : ℂ) * absPower (z + w) _
  simp only [absPower_apply, Complex.cpow_add _ _ (absPower_base_ne_zero _)]
  ring

/-- Smoothness of the real inducing determinant character on the general linear group. -/
theorem contMDiff_determinantWeight {n : ℕ} (c : RealCharacterData) (z : ℂ) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      (determinantWeight c z : Langlands.GeneralLinear n ℝ → ℂ) := by
  refine contMDiff_of_contDiffOn
    (ψ := fun y : Matrix (Fin n) (Fin n) ℝ => (((y.det / |y.det| : ℝ) : ℂ) ^ c.parity.val) *
      ((|y.det| : ℝ) : ℂ) ^ (c.exponent + z)) ?_ ?_
  · intro y hy
    have hdet : y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det y).mp hy).ne_zero
    have hd : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℝ => x.det) :=
      PrincipalSeriesExtension.contDiff_det_comp fun i j =>
        PrincipalSeriesExtension.contDiff_entry i j
    have ha : ContDiffAt ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℝ => |x.det|) y :=
      (contDiffAt_abs hdet).comp y hd.contDiffAt
    have hs := (Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (hd.contDiffAt.div ha (abs_ne_zero.mpr hdet))).pow c.parity.val
    exact (hs.mul (PrincipalSeriesExtension.contDiffAt_ofReal_cpow ha
      (abs_pos.mpr hdet) (c.exponent + z))).contDiffWithinAt
  · intro g
    change (c.character (Matrix.GeneralLinearGroup.det g) : ℂ) *
      absPower z (Matrix.GeneralLinearGroup.det g) = _
    rw [c.character_eq, absPower_apply, mul_assoc,
      ← Complex.cpow_add _ _ (absPower_base_ne_zero (Matrix.GeneralLinearGroup.det g))]
    rfl

private def tailMatrix (a : Y) : M := fun i j => a i.succ j.succ

private theorem tailMatrix_unipotent (u : upperUnipotent (m + 1) ℝ) :
    (tailMatrix u.val.val).IsUpperTriangular ∧ ∀ i, tailMatrix u.val.val i i = 1 :=
  ⟨fun _ _ h => u.property.1 (Fin.succ_lt_succ_iff.mpr h), fun i => u.property.2 i.succ⟩

private theorem det_one_of_unipotent_matrix {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (h : a.IsUpperTriangular) (hdiag : ∀ i, a i i = 1) : a.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hdiag]

private theorem tailMatrix_isUnit (u : upperUnipotent (m + 1) ℝ) :
    IsUnit (tailMatrix u.val.val) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (det_one_of_unipotent_matrix _ (tailMatrix_unipotent u).1
      (tailMatrix_unipotent u).2 ▸ isUnit_one)

private def tailUnipotent (u : upperUnipotent (m + 1) ℝ) : upperUnipotent m ℝ :=
  ⟨(tailMatrix_isUnit u).unit, by
    change (tailMatrix_isUnit u).unit.val.IsUpperTriangular ∧
      ∀ i, (tailMatrix_isUnit u).unit.val i i = 1
    rw [(tailMatrix_isUnit u).unit_spec]
    exact tailMatrix_unipotent u⟩

private theorem det_unipotent {n : ℕ} (u : upperUnipotent n ℝ) :
    Matrix.GeneralLinearGroup.det u.val = 1 :=
  Units.ext (det_one_of_unipotent_matrix _ u.property.1 u.property.2)

private theorem det_diagonal {n : ℕ} (a : Fin n → ℝˣ) :
    Matrix.GeneralLinearGroup.det (Iwasawa.diagonalUnits a) = ∏ i, a i := by
  apply Units.ext
  simp [Iwasawa.diagonalUnits_val, Matrix.det_diagonal]

private def tailBorel (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) : G :=
  Iwasawa.diagonalUnits (Fin.tail a) * (tailUnipotent u).val

private theorem det_tailBorel (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) :
    Matrix.GeneralLinearGroup.det (tailBorel a u) = ∏ i : Fin m, a i.succ := by
  simp [tailBorel, map_mul, det_unipotent, det_diagonal, Fin.tail]

private theorem det_borel_eq (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) :
    Matrix.GeneralLinearGroup.det (Iwasawa.diagonalUnits a * u.val) =
      a 0 * Matrix.GeneralLinearGroup.det (tailBorel a u) := by
  rw [map_mul, det_unipotent, mul_one, det_diagonal, Fin.prod_univ_succ, det_tailBorel]

private theorem rowPoint_borel (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
    (h : G) (g : H) :
    rowPoint h.val (Iwasawa.diagonalUnits a * u.val * g) =
      rowPoint (h * tailBorel a u).val g := by
  let b : H := Iwasawa.diagonalUnits a * u.val
  let t := tailBorel a u
  have hzero : ∀ i : Fin m, b.val i.succ 0 = 0 := by
    intro i
    have h0 : u.val.val i.succ (0 : Fin (m + 1)) = 0 := u.property.1 (Fin.succ_pos i)
    simp only [b, Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
    change (a i.succ : ℝ) * u.val.val i.succ 0 = 0
    rw [h0, mul_zero]
  have htail (i j : Fin m) : b.val i.succ j.succ = t.val i j := by
    simp only [b, t, tailBorel, Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
    change (a i.succ : ℝ) * u.val.val i.succ j.succ =
      (a i.succ : ℝ) * (tailMatrix_isUnit u).unit.val i j
    rw [(tailMatrix_isUnit u).unit_spec]
    rfl
  have hrows : lastRows (b * g).val = t.val * lastRows g.val := by
    ext i j
    change (b.val * g.val) i.succ j = (t.val * lastRows g.val) i j
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, hzero, zero_mul, zero_add, htail, lastRows]
  change h.val * lastRows (b * g).val = (h.val * t.val) * lastRows g.val
  rw [hrows, Matrix.mul_assoc]

private theorem principalSeriesCharacter_head (c : RealCharacterData) (ds : List RealBlock)
    (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) :
    principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) a *
      absPower (1 / 2) (Matrix.GeneralLinearGroup.det (tailBorel a u)) =
    scalarWeight c ((m : ℂ) / 2) (a 0) *
      principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a) := by
  rw [det_tailBorel, map_prod]
  simp only [principalSeriesCharacter, Fin.prod_univ_succ, realPositionCharacter,
    Real.norm_eq_abs, Module.finrank_self, pow_one,
    Fin.val_zero, Nat.cast_zero, sub_zero, Nat.cast_succ, add_sub_cancel_right,
    Fin.val_succ, Fin.tail, scalarWeight, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [absPower_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (absPower_base_ne_zero (a i.succ))]
  congr 2
  ring

private theorem godement_factor_identity (c : RealCharacterData) (ds : List RealBlock)
    (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) :
    determinantWeight c ((m : ℂ) / 2) (Iwasawa.diagonalUnits a * u.val) *
      principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a) =
    principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) a *
      determinantWeight c (((m : ℂ) + 1) / 2) (tailBorel a u) := by
  rw [show determinantWeight c ((m : ℂ) / 2) (Iwasawa.diagonalUnits a * u.val) =
      scalarWeight c ((m : ℂ) / 2) (a 0) *
        determinantWeight c ((m : ℂ) / 2) (tailBorel a u) from by
    change scalarWeight c _ (Matrix.GeneralLinearGroup.det _) = _
    rw [det_borel_eq, map_mul]
    rfl]
  rw [mul_right_comm, ← principalSeriesCharacter_head c ds a u, mul_assoc,
    determinantWeight_add_shift, show (m : ℂ) / 2 + 1 / 2 = ((m : ℂ) + 1) / 2 by ring]

section Integral

variable [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
  [BorelSpace (Langlands.GeneralLinear m ℝ)]
  (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
  [Measure.IsMulRightInvariant μ]

private def lowerMultiplier (c : RealCharacterData) (f : G → ℂ) (h : G) : ℂ :=
  f (h⁻¹) * determinantWeight c (((m : ℂ) + 1) / 2) h

/-- The compact-support Godement section from the lower-rank position principal series. -/
def sectionValue (c : RealCharacterData) (f : G → ℂ) (Φ : X → ℂ) (g : H) : ℂ :=
  determinantWeight c ((m : ℂ) / 2) g * innerIntegral μ Φ (lowerMultiplier c f) g

omit [MeasurableSpace G] [BorelSpace G] [Measure.IsMulRightInvariant μ] [IsFiniteMeasureOnCompacts μ] in
private theorem weighted_kernel_borel (c : RealCharacterData) (ds : List RealBlock)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (Φ : X → ℂ) (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) (g : H) (h : G) :
    let t := tailBorel a u
    let b : H := Iwasawa.diagonalUnits a * u.val
    let δ := determinantWeight (n := m) c (((m : ℂ) + 1) / 2)
    let A := lowerMultiplier c f
    δ t * (A h * Φ (rowPoint h.val (b * g))) =
      principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a) *
        (A (h * t) * Φ (rowPoint (h * t).val g)) := by
  intro t b δ A
  let lowerCharacter := principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a)
  have hSource : f (h⁻¹) = lowerCharacter * f ((h * t)⁻¹) := by
    calc
      _ = f (t * (h * t)⁻¹) := by rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = _ := hf.2 (Fin.tail a) (tailUnipotent u) ((h * t)⁻¹)
  rw [show rowPoint h.val (b * g) = rowPoint (h * t).val g from rowPoint_borel a u h g]
  change δ t * (f (h⁻¹) * δ h * Φ _) =
    lowerCharacter * (f ((h * t)⁻¹) * δ (h * t) * Φ _)
  rw [map_mul, hSource]
  ring

omit [IsFiniteMeasureOnCompacts μ] in
private theorem weighted_inner_borel (c : RealCharacterData) (ds : List RealBlock)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (Φ : X → ℂ) (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) (g : H) :
    determinantWeight c (((m : ℂ) + 1) / 2) (tailBorel a u) *
      innerIntegral μ Φ (lowerMultiplier c f) (Iwasawa.diagonalUnits a * u.val * g) =
    principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a) *
      innerIntegral μ Φ (lowerMultiplier c f) g := by
  let t := tailBorel a u
  let b : H := Iwasawa.diagonalUnits a * u.val
  let lowerCharacter := principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a)
  let δ := determinantWeight (n := m) c (((m : ℂ) + 1) / 2)
  let A := lowerMultiplier c f
  change δ t * innerIntegral μ Φ A (b * g) = lowerCharacter * innerIntegral μ Φ A g
  unfold innerIntegral
  rw [← integral_const_mul, ← integral_const_mul]
  calc
    _ = ∫ h, lowerCharacter * (A (h * t) * Φ (rowPoint (h * t).val g)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (weighted_kernel_borel c ds hf Φ a u g))
    _ = _ := integral_mul_right_eq_self (μ := μ)
      (fun h : G => lowerCharacter * (A h * Φ (rowPoint h.val g))) t

/-- The lower-group integral of the absolute Godement kernel, including the outer weight. -/
def absoluteSectionValue (c : RealCharacterData) (f : G → ℂ) (Φ : X → ℂ) (g : H) : ℝ :=
  ‖determinantWeight c ((m : ℂ) / 2) g‖ *
    ∫ h, ‖lowerMultiplier c f h * Φ (rowPoint h.val g)‖ ∂μ

omit [IsFiniteMeasureOnCompacts μ] in
/-- The absolute section transforms by the norm of the upper inducing character. -/
theorem absoluteSectionValue_covariant (c : RealCharacterData) (ds : List RealBlock)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (Φ : X → ℂ) (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) (g : H) :
    absoluteSectionValue μ c f Φ (Iwasawa.diagonalUnits a * u.val * g) =
      ‖principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) a‖ *
        absoluteSectionValue μ c f Φ g := by
  let t := tailBorel a u
  let b : H := Iwasawa.diagonalUnits a * u.val
  let A := lowerMultiplier c f
  let p := determinantWeight (n := m + 1) c ((m : ℂ) / 2)
  let w := determinantWeight c (((m : ℂ) + 1) / 2) t
  let lowerCharacter := principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a)
  let upperCharacter := principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) a
  let I := fun q : H => ∫ h, ‖A h * Φ (rowPoint h.val q)‖ ∂μ
  have hI : ‖w‖ * I (b * g) = ‖lowerCharacter‖ * I g := by
    unfold I
    rw [← integral_const_mul, ← integral_const_mul]
    calc
      _ = ∫ h, (fun x : G => ‖lowerCharacter‖ * ‖A x * Φ (rowPoint x.val g)‖) (h * t) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun h => ?_)
        simpa only [norm_mul] using congrArg norm (weighted_kernel_borel c ds hf Φ a u g h)
      _ = _ := integral_mul_right_eq_self (μ := μ)
        (fun x : G => ‖lowerCharacter‖ * ‖A x * Φ (rowPoint x.val g)‖) t
  have hFactor : ‖p b‖ * ‖lowerCharacter‖ = ‖upperCharacter‖ * ‖w‖ := by
    simpa only [norm_mul] using congrArg norm (godement_factor_identity c ds a u)
  apply mul_left_cancel₀ (norm_ne_zero_iff.mpr (determinantWeight_ne_zero c _ t))
  change ‖w‖ * (‖p (b * g)‖ * I (b * g)) = ‖w‖ * (‖upperCharacter‖ * (‖p g‖ * I g))
  rw [map_mul, norm_mul]
  calc
    _ = ‖p b‖ * (‖p g‖ * (‖w‖ * I (b * g))) := by ring
    _ = (‖p b‖ * ‖lowerCharacter‖) * (‖p g‖ * I g) := by rw [hI]; ring
    _ = _ := by rw [hFactor]; ring

omit [IsFiniteMeasureOnCompacts μ] in
/-- The complex Godement section transforms by the upper inducing character. -/
theorem sectionValue_covariant (c : RealCharacterData) (ds : List RealBlock)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (Φ : X → ℂ) (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ) (g : H) :
    sectionValue μ c f Φ (Iwasawa.diagonalUnits a * u.val * g) =
      principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) a *
        sectionValue μ c f Φ g := by
  let t := tailBorel a u
  let b : Langlands.GeneralLinear (m + 1) ℝ := Iwasawa.diagonalUnits a * u.val
  let p := determinantWeight (n := m + 1) c ((m : ℂ) / 2)
  let w := determinantWeight c (((m : ℂ) + 1) / 2) t
  let I := innerIntegral μ Φ (lowerMultiplier c f)
  let lowerCharacter := principalSeriesCharacter ℝ m (realPositionCharacter ds) (Fin.tail a)
  let upperCharacter :=
    principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) a
  have hI : w * I (b * g) = lowerCharacter * I g := weighted_inner_borel μ c ds hf Φ a u g
  have hFactor : p b * lowerCharacter = upperCharacter * w := godement_factor_identity c ds a u
  apply mul_left_cancel₀ (determinantWeight_ne_zero c _ t)
  change w * (p (b * g) * I (b * g)) = w * (upperCharacter * (p g * I g))
  rw [map_mul]
  calc
    _ = p b * (p g * (w * I (b * g))) := by ring
    _ = (p b * lowerCharacter) * (p g * I g) := by rw [hI]; ring
    _ = _ := by rw [hFactor]; ring

/-- Godement's construction from a compact full-row-rank test yields a smooth
vector in the position principal series with the given leading character. -/
def RealGodementSectionStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsMulRightInvariant μ] (c : RealCharacterData) (ds : List RealBlock)
    (f : Langlands.GeneralLinear m ℝ → ℂ),
    f ∈ principalSeries ℝ m (realPositionCharacter ds) →
  ∀ (S : Set (Matrix (Fin m) (Fin (m + 1)) ℝ)), IsCompact S →
    (∀ x ∈ S, HasFullRowRank x) →
  ∀ (Φ : Matrix (Fin m) (Fin (m + 1)) ℝ → ℂ), ContDiff ℝ ∞ Φ →
    (∀ x ∉ S, Φ x = 0) →
    sectionValue μ c f Φ ∈
      principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))

theorem realGodementSection : RealGodementSectionStatement := by
  intro m _ _ μ _ _ c ds f hf S hS hRank Φ hΦ hΦS
  refine ⟨?_, ?_⟩
  · have hη : Continuous (lowerMultiplier c f) :=
      (hf.1.continuous.comp continuous_inv).mul (contMDiff_determinantWeight c _).continuous
    have hPair := (contMDiff_determinantWeight (n := m + 1) c ((m : ℂ) / 2)).prodMk
      (realGodementSmooth m μ S hS hRank Φ (lowerMultiplier c f) hΦ hΦS hη)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hPair
    have hMul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_fst.mul contDiff_snd
    exact hMul.comp_contMDiff hPair
  · exact sectionValue_covariant μ c ds hf Φ

end Integral

end Langlands.Global.RankinSelbergGlobal.RealGodement
