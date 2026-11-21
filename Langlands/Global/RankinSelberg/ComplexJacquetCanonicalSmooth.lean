import Langlands.Global.RankinSelberg.ComplexLocalRectangularBounds
import Langlands.Global.RankinSelberg.ComplexJacquetIntegratedLie
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerFiniteGrowth
import Mathlib.Analysis.Normed.Ring.Units

/-! # Smoothness and right Lie equivariance of canonical Jacquet evaluation -/

noncomputable section

open Filter MeasureTheory Set
open scoped Classical ContDiff Interval Manifold Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean (complexStandardLie contMDiff_of_contDiffOn matrixModel unitaryCompact
  rightDerivative rightDerivative_eq_fderiv unitsExtension unitsExtension_val principalSeriesLie_one_tmul_apply_coe)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (characterList compactRestriction_isCompactProfile)
open ComplexLocalIwasawa (alpha bpart exp_alpha kpart npart)
open ComplexLocalWhittakerGauge (logTorus logTorus_inv_val)
open ComplexPlaceAnalytic (complexMatrixHeight_inv norm_entry_le_complexMatrixHeight)
open ComplexCharacterChange (complexMatrixHeight_mul_le)

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "P" => (I → ℂ)
local notation "M" => Matrix I I ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)
local notation "J" => Fin (Module.finrank ℝ M)

private def lieDirection (l : I → ℤ) (p : P) (f : Std[l, p]) : M →ₗ[ℝ] Std[l, p] :=
  (((LinearMap.applyₗ (R := ℂ) (M₂ := Std[l, p]) f).comp
    (complexStandardLie n (characterList l p)).toLinearMap).restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ M 1)

private theorem lieDirection_apply (l : I → ℤ) (p : P) (f : Std[l, p]) (X : M) :
    lieDirection l p f X = complexStandardLie n (characterList l p) (1 ⊗ₜ X) f := rfl

private def matrixBasis : Module.Basis J ℝ M := Module.finBasis ℝ M

private def fieldCoord (i : J) : M →L[ℝ] M →L[ℝ] ℂ :=
  (ContinuousLinearMap.compL ℝ M M ℂ
    (Complex.ofRealCLM.comp ((matrixBasis (r := r)).coord i).toContinuousLinearMap)).comp
      (ContinuousLinearMap.mul ℝ M)

private def invCoord (i : J) (x : M) : M →L[ℝ] ℂ := fieldCoord i (Ring.inverse x)

private theorem invCoord_apply (i : J) (x Y : M) :
    invCoord i x Y = (((matrixBasis (r := r)).repr (Ring.inverse x * Y) i : ℝ) : ℂ) := rfl

private theorem contDiffOn_invCoord (i : J) {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (invCoord i) {x : M | IsUnit x} := by
  rintro _ ⟨u, rfl⟩
  exact ((fieldCoord i).contDiff.contDiffAt.comp _ (contDiffAt_ringInverse ℝ u)).contDiffWithinAt

private def candidateDerivative (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P)
    (f : Std[l, p]) (x : M) : M →L[ℝ] ℂ :=
  ∑ i : J, unitsExtension (continuedJacquet μ a l p
    (lieDirection l p f (matrixBasis i))) x • invCoord i x

private theorem candidateDerivative_apply (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P)
    (f : Std[l, p]) (g : G) (Y : M) :
    candidateDerivative μ a l p f g.val Y =
      continuedJacquet μ a l p (lieDirection l p f (g⁻¹.val * Y)) g := by
  let e := matrixBasis (r := r)
  conv_rhs => rw [← e.sum_repr (g⁻¹.val * Y)]
  simp only [candidateDerivative, sum_apply, smul_apply,
    smul_eq_mul, unitsExtension_val, invCoord_apply, Ring.inverse_unit, map_sum, map_smul,
    LinearMap.map_smul_of_tower, Finset.sum_apply, Pi.smul_apply, Complex.real_smul, e]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private theorem continuous_candidateDerivative (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P)
    (f : Std[l, p]) : Continuous (fun g : G => candidateDerivative μ a l p f g.val) := by
  apply continuous_finsetSum
  intro i _
  have hc := (canonicalJacquetFamily_properties μ a l _
    (compactRestriction_isCompactProfile (lieDirection l p f (matrixBasis i)).2)).1 p
  have hInv : Continuous (fun g : G => invCoord i g.val) :=
    ((contDiffOn_invCoord i (k := 0)).continuousOn.comp_continuous Units.continuous_val fun g => g.isUnit)
  simp only [unitsExtension_val]
  exact hc.smul hInv

private theorem hasFDerivAt_canonicalJacquet (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P)
    (f : Std[l, p]) (g : G) : HasFDerivAt (unitsExtension (continuedJacquet μ a l p f))
      (candidateDerivative μ a l p f g.val) g.val := by
  let W := continuedJacquet μ a l p f
  let F := unitsExtension W
  let L (h : G) := candidateDerivative μ a l p f h.val
  change HasFDerivAt F (L g) g.val
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let U : Set G := {h | ‖L h - L g‖ < ε}
  have hU : IsOpen U := isOpen_lt ((continuous_candidateDerivative μ a l p f).sub continuous_const).norm
    continuous_const
  have hg : g ∈ U := by simpa [U] using hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (Units.isOpenEmbedding_val.isOpenMap U hU)
    g.val (show g.val ∈ Units.val '' U from ⟨g, hg, rfl⟩)
  filter_upwards [Metric.ball_mem_nhds g.val hδ] with y hy
  let Z := y - g.val
  let clip (t : ℝ) := max 0 (min t 1)
  let x (t : ℝ) := g.val + clip t • Z
  have hx (t : ℝ) : x t ∈ Metric.ball g.val δ := by
    have hc₀ : 0 ≤ clip t := le_max_left _ _
    have hc₁ : clip t ≤ 1 := max_le zero_le_one (min_le_right _ _)
    have hy' : ‖Z‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm, Z] using hy
    rw [Metric.mem_ball, dist_eq_norm, show x t - g.val = clip t • Z by simp [x], norm_smul,
      Real.norm_of_nonneg hc₀]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc₁).trans_lt hy'
  have hu (t : ℝ) : IsUnit (x t) := by
    obtain ⟨h, _, he⟩ := hball (hx t)
    exact he ▸ h.isUnit
  let γ (t : ℝ) := (hu t).unit
  have hγval (t : ℝ) : (γ t).val = x t := (hu t).unit_spec
  have hγc : Continuous γ := by
    apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
    change Continuous (fun t => (γ t).val)
    simp_rw [hγval]
    exact continuous_const.add (((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).max
      (continuous_id.min continuous_const)).smul continuous_const)
  let V (t : ℝ) := (γ t)⁻¹.val * Z
  have hV : Continuous V := ((Units.continuous_val.comp (continuous_inv.comp hγc))).mul continuous_const
  have hγd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun s => (γ s).val) ((γ t).val * V t) t := by
    have hZ : (γ t).val * V t = Z := by
      rw [show V t = (γ t)⁻¹.val * Z from rfl, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [hZ]
    have hd : HasDerivAt (fun s : ℝ => g.val + s • Z) Z t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const Z).const_add g.val
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [hγval]
    change g.val + clip s • Z = g.val + s • Z
    rw [show clip s = s from (congrArg (max 0) (min_eq_left hs.2.le)).trans (max_eq_right hs.1.le)]
  have hγ₀ : γ 0 = g := by
    apply Units.ext
    rw [hγval]
    simp [x, clip]
  have hγ₁ : (γ 1).val = y := by
    rw [hγval]
    simp only [x, clip, min_self, max_eq_right zero_le_one, one_smul, Z]
    abel
  have hL (t : ℝ) : L (γ t) Z = continuedJacquet μ a l p
      (complexStandardLie n (characterList l p) (1 ⊗ₜ (V t)) f) (γ t) := by
    exact candidateDerivative_apply μ a l p f (γ t) Z
  have hInt : (∫ t in (0 : ℝ)..1, L (γ t) Z) = F y - F g.val := by
    simp_rw [hL]
    rw [complexJacquetIntegratedLie μ a l p f γ V hγc hV 0 1 zero_le_one hγd, hγ₀]
    rw [← hγ₁, show F = unitsExtension W from rfl, unitsExtension_val, unitsExtension_val]
  let E (t : ℝ) := (L (γ t) - L g) Z
  have hc : Continuous (fun t => L (γ t)) := (continuous_candidateDerivative μ a l p f).comp hγc
  have hE : (∫ t in (0 : ℝ)..1, E t) = F y - F g.val - L g Z := by
    change (∫ t in (0 : ℝ)..1, L (γ t) Z - L g Z) = _
    have hI : IntervalIntegrable (fun t => L (γ t) Z) volume 0 1 :=
      (hc.clm_apply continuous_const).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const, hInt, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
  rw [← hE]
  have hB : ∀ t ∈ Ι (0 : ℝ) 1, ‖E t‖ ≤ ε * ‖Z‖ := by
    intro t _
    obtain ⟨h, hh, he⟩ := hball (hx t)
    have he' : h = γ t := Units.ext (he.trans (hγval t).symm)
    subst h
    exact ((L (γ t) - L g).le_opNorm Z).trans (mul_le_mul_of_nonneg_right hh.le (norm_nonneg _))
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hB

private theorem contDiffOn_canonicalJacquet (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P)
    (f : Std[l, p]) : ContDiffOn ℝ ∞ (unitsExtension (continuedJacquet μ a l p f)) {x : M | IsUnit x} := by
  apply contDiffOn_infty.mpr
  intro k
  induction k generalizing f with
  | zero =>
    apply contDiffOn_zero.mpr
    rintro _ ⟨g, rfl⟩
    exact (hasFDerivAt_canonicalJacquet μ a l p f g).continuousAt.continuousWithinAt
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen Units.isOpen).mpr ⟨?_, ?_, ?_⟩
    · rintro _ ⟨g, rfl⟩
      exact (hasFDerivAt_canonicalJacquet μ a l p f g).differentiableAt.differentiableWithinAt
    · exact fun h => absurd h (WithTop.natCast_ne_top k)
    · refine ContDiffOn.congr (f := candidateDerivative μ a l p f) ?_ ?_
      · exact ContDiffOn.sum fun i _ => (ih _).fun_smul (contDiffOn_invCoord i)
      · rintro _ ⟨g, rfl⟩
        exact (hasFDerivAt_canonicalJacquet μ a l p f g).fderiv

/-- The canonical Jacquet values are smooth and evaluation commutes with the standard right
Lie operator for every inducing parameter. -/
def ComplexJacquetCanonicalSmoothStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P) (f : Std[l, p]),
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (continuedJacquet μ a l p f) ∧
    ∀ X : M, continuedJacquet μ a l p (complexStandardLie n (characterList l p) (1 ⊗ₜ X) f) =
      rightDerivative (matrixModel ℂ n) X (continuedJacquet μ a l p f)

theorem complexJacquetCanonicalSmooth : ComplexJacquetCanonicalSmoothStatement (r := r) := by
  intro μ a l p f
  have hs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (continuedJacquet μ a l p f) :=
    contMDiff_of_contDiffOn (contDiffOn_canonicalJacquet μ a l p f)
      (fun g => (unitsExtension_val (continuedJacquet μ a l p f) g).symm)
  refine ⟨hs, fun X => ?_⟩
  funext g
  rw [rightDerivative_eq_fderiv hs, (hasFDerivAt_canonicalJacquet μ a l p f g).fderiv,
    candidateDerivative_apply, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
    lieDirection_apply]

private theorem exists_height_bound_exp_abs_alpha :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : G) (i : I), Real.exp |alpha g i| ≤ C * complexMatrixHeight g := by
  have hc : ContinuousOn (complexMatrixHeight : G → ℝ) (unitaryCompact ℂ n) :=
    continuous_complexMatrixHeight.continuousOn
  obtain ⟨C, hC⟩ := (Langlands.Archimedean.ComplexDuality.isCompact_unitaryCompact n).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun g i => ?_⟩
  have hH : ∀ h : G, 0 ≤ complexMatrixHeight h := by
    intro h
    unfold complexMatrixHeight
    positivity
  have hk := hC ((kpart g)⁻¹).val ((kpart g)⁻¹).2
  rw [Real.norm_of_nonneg (hH _)] at hk
  have hb : complexMatrixHeight (bpart g) ≤ complexMatrixHeight g * max C 0 :=
    (complexMatrixHeight_mul_le g (kpart g).val⁻¹).trans
      (mul_le_mul_of_nonneg_left (hk.trans (le_max_left _ _)) (hH g))
  have hn : 0 < n := Nat.succ_pos _
  have hpos := norm_entry_le_complexMatrixHeight hn (bpart g) i i
  have hneg := norm_entry_le_complexMatrixHeight hn (bpart g)⁻¹ i i
  rw [← exp_alpha g i, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hpos
  rw [← ComplexLocalRectangularBounds.exp_neg_alpha g i, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
    complexMatrixHeight_inv] at hneg
  rw [mul_comm]
  obtain hi | hi := le_total 0 (alpha g i)
  · rw [abs_of_nonneg hi]
    exact hpos.trans hb
  · rw [abs_of_nonpos hi]
    exact hneg.trans hb

private theorem canonicalJacquet_moderateGrowth (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : I → ℤ) (p : P) (f : Std[l, p]) :
    ∃ (C : ℝ) (N : ℕ), ∀ g : G,
      ‖continuedJacquet μ a l p f g‖ ≤ C * complexMatrixHeight g ^ N := by
  obtain ⟨B, hB, hα⟩ := exists_height_bound_exp_abs_alpha (r := r)
  have hJ := canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile f.2)
  obtain ⟨δ, hδ, N, hN⟩ := hJ.2.2.1 p
  obtain ⟨C, hC₀, hC⟩ := hN 0
  refine ⟨C * B ^ (n * N), n * N, fun g => ?_⟩
  have h := hC p (Metric.mem_ball_self hδ) g
  change ‖continuedJacquet μ a l p f g‖ ≤ _
  simp only [Nat.cast_zero, zero_mul, sub_zero] at h
  have hE : Real.exp ((N : ℝ) * ∑ i, |alpha g i|) ≤ (B * complexMatrixHeight g) ^ (n * N) := by
    rw [Real.exp_nat_mul, Real.exp_sum, pow_mul]
    apply pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _) _ N
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => Real.exp_nonneg |alpha g i|)
        (fun i _ => hα g i))
  exact h.trans (by simpa only [mul_pow, ← mul_assoc] using mul_le_mul_of_nonneg_left hE hC₀)

/-- The canonical continuation is a Whittaker intertwiner for every inducing parameter. -/
def ComplexJacquetCanonicalIntertwinerStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P),
    IsComplexWhittakerIntertwiner r (characterList l p) (-a) (continuedJacquet μ a l p)

theorem complexJacquetCanonicalIntertwiner : ComplexJacquetCanonicalIntertwinerStatement (r := r) := by
  intro μ a l p
  have he := complexJacquetEvaluation (r := r) μ a l p
  refine ⟨fun f u hu g => he.1 f ⟨u, hu⟩ g, fun f => (complexJacquetCanonicalSmooth μ a l p f).1,
    canonicalJacquet_moderateGrowth μ a l p, he.2.1, ?_⟩
  intro X f f' h
  have hf' : f' = complexStandardLie n (characterList l p) (1 ⊗ₜ X) f :=
    Subtype.ext (h.trans (principalSeriesLie_one_tmul_apply_coe ℂ n _ X f).symm)
  rw [hf']
  exact (complexJacquetCanonicalSmooth μ a l p f).2 X

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
