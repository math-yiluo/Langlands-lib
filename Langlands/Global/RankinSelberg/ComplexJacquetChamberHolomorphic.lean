import Langlands.Global.RankinSelberg.ComplexJacquetChamberConvergence
import Langlands.Global.RankinSelberg.ComplexGodementJacquetComparison
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Holomorphy of the complex Jacquet integral in the strict chamber -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberHolomorphic

open Langlands.Archimedean.UnitaryFinitePolynomial (compactSpace_unitary)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val norm_phaseUnit)
open Langlands.Archimedean.ComplexPartialJacquet (IsPhasePower IsStrictlyDominant)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extension extension_iwasawa phaseMatrix phaseMatrix_val)
open Langlands.Archimedean.GramFormula (shiftedExponent)
open Langlands.GeneralLinear (weylLong)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (complexScaledCharacter)
open ComplexLocalIwasawa (alpha continuous_alpha kpart continuous_kpart npart npart_mul_logTorus_mul_kpart
  conjTorus conjTorus_val logTorus_neg)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexJacquetChamberConvergence (radialChar sphericalMajorant sphericalMajorant_mem complexJacquetOpenCellConvergence)
open ComplexJacquetUnipotentMeasure (entryHaar)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℂ
local notation "P" => (Fin (r + 1) → ℂ)
local notation "w" => weylLong (r + 1) ℂ

/-- The strict chamber in the finite-dimensional space of inducing exponents. -/
def chamber (r : ℕ) : Set (Fin (r + 1) → ℂ) :=
  {p | ∀ i : Fin r, (p i.succ).re < (p i.castSucc).re}

theorem isOpen_chamber : IsOpen (chamber r) := by
  have h : chamber r = ⋂ i : Fin r, {p : P | (p i.succ).re < (p i.castSucc).re} := by
    ext p
    simp [chamber]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (Complex.continuous_re.comp (continuous_apply _))
    (Complex.continuous_re.comp (continuous_apply _))

private def extendExponents (p : P) (j : ℕ) : ℂ :=
  if h : j < r + 1 then p ⟨j, h⟩ else 0

private theorem extendExponents_apply (p : P) (i : Fin (r + 1)) : extendExponents p i = p i := by
  simp [extendExponents, i.isLt]

private theorem strict_extendExponents (p : P) (hp : p ∈ chamber r) :
    IsStrictlyDominant (extendExponents p) r := by
  intro j hj
  let i : Fin r := ⟨j, hj⟩
  change (extendExponents p i.succ).re < (extendExponents p i.castSucc).re
  simpa only [extendExponents_apply] using hp i

private def rho : P := fun i => ((r + 1 : ℕ) - 1 : ℂ) / 2 - ((i : ℕ) : ℂ)

private theorem add_rho_eq_shifted (p : P) : p + rho = shiftedExponent (r + 1) (extendExponents p) := by
  ext i
  simp [rho, shiftedExponent, extendExponents_apply]

private def compactPart (x : G) : U := ⟨(kpart x).val.val, (kpart x).property⟩

private theorem continuous_compactPart : Continuous (compactPart (r := r)) := by
  have h : Continuous fun x : G => (kpart x).val.val :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_kpart)
  exact h.subtype_mk _

private def exponentForm (x : G) : P →L[ℂ] ℂ :=
  ∑ i : Fin (r + 1), ((2 * alpha x i : ℝ) : ℂ) • ContinuousLinearMap.proj i

private theorem exponentForm_apply (x : G) (p : P) :
    exponentForm x p = ∑ i, ((2 * alpha x i : ℝ) : ℂ) * p i := by
  simp [exponentForm]

private theorem continuous_exponentForm : Continuous (exponentForm (r := r)) := by
  unfold exponentForm
  exact continuous_finsetSum _ fun i _ => (Complex.continuous_ofReal.comp
    (((continuous_apply i).comp continuous_alpha).const_mul 2)).smul continuous_const

/-- The standard compact section with fixed unitary profile and the normalized Borel shift. -/
def compactSection (p : P) (φ : U → ℂ) (x : G) : ℂ := extension (p + rho) φ x

private theorem compactSection_eq (p : P) (φ : U → ℂ) (x : G) :
    compactSection p φ x = Complex.exp (exponentForm x (p + rho)) * φ (compactPart x) := by
  let y := alpha x
  let a : Fin (r + 1) → ℂˣ := fun i => Units.mk0 (Real.exp (y i) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  let u := conjTorus (-y) (npart x)
  have hx : GeneralLinear.Iwasawa.diagonalUnits a * u.val * (kpart x).val = x := by
    change logTorus y * (conjTorus (-y) (npart x)).val * (kpart x).val = _
    rw [conjTorus_val, logTorus_neg, inv_inv]
    calc
      _ = (npart x).val * logTorus y * (kpart x).val := by group
      _ = x := npart_mul_logTorus_mul_kpart x
  have haNorm (i : Fin (r + 1)) : ‖(a i : ℂ)‖ = Real.exp (y i) := by
    exact Complex.norm_of_nonneg (Real.exp_pos _).le
  have haPhase : phaseMatrix a = 1 := by
    have h (i : Fin (r + 1)) : phaseUnit (a i) = 1 := by
      apply Units.ext
      rw [phaseUnit_val, haNorm]
      exact div_self (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    apply Subtype.ext
    simp [phaseMatrix_val, h, Matrix.diagonal_one]
  have he := extension_iwasawa (p + rho) φ a u (kpart x).property
  rw [hx, haPhase, one_mul] at he
  rw [compactSection, he, exponentForm_apply, Complex.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [haNorm, ← Real.exp_nat_mul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), ← Complex.ofReal_log (Real.exp_pos _).le,
    Real.log_exp]
  norm_num [y]

private def radialSize (p : P) (x : G) : ℝ := Real.exp (exponentForm x (p + rho)).re

private theorem radialSize_eq_spherical (p : P) (x : G) :
    radialSize p x = ‖sphericalMajorant (r + 1) (fun i => (extendExponents p i).re) x‖ := by
  let q : P := fun i => ((p i).re : ℂ)
  have hq (j : ℕ) : extendExponents q j = ((extendExponents p j).re : ℂ) := by
    by_cases hj : j < r + 1 <;> simp [q, extendExponents, hj]
  have hnorm : radialSize q x = radialSize p x := by
    unfold radialSize
    congr 1
    simp [exponentForm_apply, Complex.re_sum, q, Pi.add_apply, Complex.add_re]
  rw [← hnorm, sphericalMajorant, show (fun l => (((extendExponents p l).re : ℝ) : ℂ)) =
    extendExponents q by funext l; exact (hq l).symm, ← add_rho_eq_shifted]
  rw [← compactSection, compactSection_eq, mul_one, Complex.norm_exp]
  rfl

private theorem integrable_radialSize (μ : AdditiveHaarMeasure ℂ) (p : P) (hp : p ∈ chamber r) (g : G) :
    Integrable (fun u : N => radialSize p (w * u.val * g)) (entryHaar μ (r + 1)) := by
  let t : ℕ → ℝ := fun i => (extendExponents p i).re
  have hrad : IsPhasePower (radialChar t) (fun i => (t i : ℂ)) := {
    eq := by intro i z; simp [radialChar, norm_phaseUnit]
    one := by intro i; simp [radialChar]
    norm_phase := by intro i z; simp [radialChar, norm_phaseUnit] }
  have hs : IsStrictlyDominant (fun i => (t i : ℂ)) r := by
    simpa only [IsStrictlyDominant, Complex.ofReal_re, t] using strict_extendExponents p hp
  simpa only [radialSize_eq_spherical] using
    (complexJacquetOpenCellConvergence r μ _ _ hrad hs _ (sphericalMajorant_mem _ t).1 g).norm

private def logSize (x : G) : ℝ := ∑ i : Fin (r + 1), |2 * alpha x i|

private theorem logSize_nonneg (x : G) : 0 ≤ logSize x := Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem norm_exponentForm_le (x : G) : ‖exponentForm x‖ ≤ logSize x := by
  apply ContinuousLinearMap.opNorm_le_bound _ (logSize_nonneg x)
  intro z
  rw [exponentForm_apply]
  calc
    ‖∑ i : Fin (r + 1), ((2 * alpha x i : ℝ) : ℂ) * z i‖ ≤
        ∑ i : Fin (r + 1), ‖((2 * alpha x i : ℝ) : ℂ) * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (r + 1), |2 * alpha x i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

private abbrev Corner (r : ℕ) := Fin (r + 1) → Bool

private def corner (p : P) (δ : ℝ) (b : Corner r) : P :=
  p + fun i => ((if b i then δ else -δ : ℝ) : ℂ)

private theorem norm_corner_sub_le (p : P) {δ : ℝ} (hδ : 0 ≤ δ) (b : Corner r) :
    ‖corner p δ b - p‖ ≤ δ := by
  refine (pi_norm_le_iff_of_nonneg hδ).2 fun i => ?_
  simp only [corner, Pi.sub_apply, Pi.add_apply, add_sub_cancel_left, Complex.norm_real]
  split <;> simp [Real.norm_of_nonneg hδ]

private theorem radialSize_le_exp (p q : P) (x : G) {δ : ℝ} (hδ : 0 ≤ δ) (h : ‖q - p‖ ≤ δ) :
    radialSize q x ≤ radialSize p x * Real.exp (δ * logSize x) := by
  have hshift : (exponentForm x (q - p)).re ≤ δ * logSize x := calc
    _ ≤ ‖exponentForm x (q - p)‖ := Complex.re_le_norm _
    _ ≤ ‖exponentForm x‖ * ‖q - p‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul h (norm_exponentForm_le x) (norm_nonneg _) hδ
  have hpq : q + rho = (p + rho) + (q - p) := by abel
  unfold radialSize
  rw [← Real.exp_add, Real.exp_le_exp, hpq, map_add, Complex.add_re]
  gcongr

private def signCorner (x : G) : Corner r := fun i => decide (0 ≤ alpha x i)

private theorem exponent_corner (p : P) (δ : ℝ) (x : G) :
    (exponentForm x (corner p δ (signCorner x) - p)).re = δ * logSize x := by
  rw [exponentForm_apply, Complex.re_sum, logSize, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ alpha x i
  · have h' : 0 ≤ 2 * alpha x i := by positivity
    simp [corner, signCorner, h, abs_of_nonneg h', mul_comm]
  · have h' : 2 * alpha x i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_ge h)
    simp [corner, signCorner, h, abs_of_nonpos h', mul_comm]

private theorem radialSize_corner (p : P) (δ : ℝ) (x : G) :
    radialSize (corner p δ (signCorner x)) x = radialSize p x * Real.exp (δ * logSize x) := by
  have hpq : corner p δ (signCorner x) + rho =
      (p + rho) + (corner p δ (signCorner x) - p) := by abel
  unfold radialSize
  rw [← Real.exp_add, hpq, map_add, Complex.add_re, exponent_corner]

private theorem radialSize_mul_logSize_le (p q : P) (x : G) {δ : ℝ} (hδ : 0 < δ)
    (h : ‖q - p‖ ≤ δ) :
    radialSize q x * logSize x ≤ δ⁻¹ * radialSize (corner p (2 * δ) (signCorner x)) x := by
  have hE : 0 ≤ logSize x := logSize_nonneg x
  have hexp : δ * logSize x ≤ Real.exp (δ * logSize x) := by
    linarith [Real.add_one_le_exp (δ * logSize x)]
  calc
    _ ≤ (radialSize p x * Real.exp (δ * logSize x)) * logSize x :=
      mul_le_mul_of_nonneg_right (radialSize_le_exp p q x hδ.le h) hE
    _ = δ⁻¹ * radialSize p x * Real.exp (δ * logSize x) * (δ * logSize x) := by
      field_simp
    _ ≤ δ⁻¹ * radialSize p x * Real.exp (δ * logSize x) * Real.exp (δ * logSize x) :=
      mul_le_mul_of_nonneg_left hexp (by unfold radialSize; positivity)
    _ = _ := by
      rw [radialSize_corner, mul_assoc (δ⁻¹ * radialSize p x), ← Real.exp_add, ← mul_assoc]
      congr 2
      ring

variable (r) in
/-- At fixed continuous compact profile and fixed group argument, the open-cell Jacquet integral
is jointly holomorphic in the inducing exponents in the strict chamber. -/
def ComplexJacquetChamberHolomorphicStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (φ : U → ℂ), Continuous φ → ∀ g : G,
    DifferentiableOn ℂ (fun p : P => openCellIntegral a (entryHaar μ (r + 1)) (compactSection p φ) g)
      (chamber r)

/-- The shifted spherical sections give a local integrable bound for the parameter derivative. -/
theorem complexJacquetChamberHolomorphic : ComplexJacquetChamberHolomorphicStatement r := by
  intro μ a φ hφ g p hp
  let ν := entryHaar μ (r + 1)
  let x : N → G := fun u => w * u.val * g
  let A : N → ℂ := fun u => φ (compactPart (x u)) * complexWhittakerCharacter a u.val
  let F (q : P) (u : N) : ℂ := Complex.exp (exponentForm (x u) (q + rho)) * A u
  let F' (q : P) (u : N) : P →L[ℂ] ℂ := F q u • exponentForm (x u)
  have hx : Continuous x := (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hθ : Continuous (fun u : N => complexWhittakerCharacter a u.val) := by
    unfold complexWhittakerCharacter
    exact (complexScaledCharacter a).continuous_complex.comp (continuous_finsetSum _ fun i _ =>
      (GeneralLinear.UpperUnipotent.entry i.castSucc i.succ).continuous)
  have hA : Continuous A := (hφ.comp (continuous_compactPart.comp hx)).mul hθ
  have hF (q : P) : Continuous (F q) :=
    (((continuous_exponentForm.comp hx).clm_apply continuous_const).cexp).mul hA
  have hF' (q : P) : Continuous (F' q) := (hF q).smul (continuous_exponentForm.comp hx)
  have hd (q : P) (u : N) : HasFDerivAt (fun z => F z u) (F' q u) q := by
    let L := exponentForm (x u)
    have h := ((L.hasFDerivAt (x := q)).add_const (L rho)).cexp.mul_const (A u)
    simpa [L, F, F', map_add, smul_smul, mul_comm] using h
  obtain ⟨C₀, hC₀⟩ := (isCompact_univ : IsCompact (Set.univ : Set U)).exists_bound_of_continuousOn hφ.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hAnorm (u : N) : ‖A u‖ ≤ C := by
    have h := hC₀ (compactPart (x u)) (mem_univ _)
    simp only [A, norm_mul, complexWhittakerCharacter, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
      mul_one]
    exact h.trans (le_max_left _ _)
  have hFnorm (q : P) (u : N) : ‖F q u‖ ≤ C * radialSize q (x u) := by
    rw [show ‖F q u‖ = radialSize q (x u) * ‖A u‖ by simp [F, radialSize, Complex.norm_exp], mul_comm C]
    exact mul_le_mul_of_nonneg_left (hAnorm u) (Real.exp_pos _).le
  have hi : Integrable (F p) ν := ((integrable_radialSize μ p hp g).const_mul C).mono'
    (hF p).aestronglyMeasurable (ae_of_all _ (hFnorm p))
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp isOpen_chamber p hp
  let δ := ε / 3
  have hδ : 0 < δ := by positivity
  have hcorners (b : Corner r) : corner p (2 * δ) b ∈ chamber r := by
    apply hεball
    rw [Metric.mem_ball, dist_eq_norm]
    exact (norm_corner_sub_le p (by positivity) b).trans_lt (by dsimp [δ]; linarith)
  let B : N → ℝ := fun u => (C * δ⁻¹) * ∑ b : Corner r, radialSize (corner p (2 * δ) b) (x u)
  have hB : Integrable B ν := by
    apply Integrable.const_mul _ (C * δ⁻¹)
    exact integrable_finsetSum _ fun b _ => integrable_radialSize μ _ (hcorners b) g
  have hbd (q : P) (hq : q ∈ Metric.ball p δ) (u : N) : ‖F' q u‖ ≤ B u := by
    have hqp : ‖q - p‖ ≤ δ := (show ‖q - p‖ < δ by simpa only [Metric.mem_ball, dist_eq_norm] using hq).le
    calc
      ‖F' q u‖ = ‖F q u‖ * ‖exponentForm (x u)‖ := norm_smul _ _
      _ ≤ (C * radialSize q (x u)) * logSize (x u) :=
        mul_le_mul (hFnorm q u) (norm_exponentForm_le (x u)) (norm_nonneg _)
          (mul_nonneg hC (Real.exp_pos _).le)
      _ ≤ (C * δ⁻¹) * radialSize (corner p (2 * δ) (signCorner (x u))) (x u) := by
        simp only [mul_assoc]
        exact mul_le_mul_of_nonneg_left (radialSize_mul_logSize_le p q (x u) hδ hqp) hC
      _ ≤ B u := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.single_le_sum (f := fun b : Corner r => radialSize (corner p (2 * δ) b) (x u))
          (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (signCorner (x u)))
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds p hδ) (Eventually.of_forall fun q => (hF q).aestronglyMeasurable)
    hi (hF' p).aestronglyMeasurable (ae_of_all _ fun u q hq => hbd q hq u) hB
    (ae_of_all _ fun u q _ => hd q u)
  have hEq : (fun q : P => openCellIntegral a ν (compactSection q φ) g) = fun q => ∫ u, F q u ∂ν := by
    funext q
    apply integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [compactSection_eq, x, F, A, mul_assoc]
  change DifferentiableWithinAt ℂ (fun q : P => openCellIntegral a ν (compactSection q φ) g) (chamber r) p
  rw [hEq]
  exact hderiv.differentiableAt.differentiableWithinAt

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberHolomorphic
