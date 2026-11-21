import Langlands.Global.RankinSelberg.RealBruhatDistributionRestriction
import Langlands.HarmonicAnalysis.Distribution.SmoothTestTimeEvaluation

/-! # Differentiating unipotent covariance of distributions on real invertible matrices -/

noncomputable section

open Filter Set TopologicalSpace Langlands.GeneralLinear
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean Real
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslationDistribution

open RealBruhatChartVanishing RealBruhatDistributionRestriction RealWhittakerGauge

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "U" => upperUnipotent (r + 1) ℝ
local notation "I" => Fin (r + 1) × Fin (r + 1)
local notation "Test" => 𝓓(invertibleDomain r, ℝ)

private def pullbackTest (A : M ≃L[ℝ] M)
    (hA : ∀ X, A X ∈ invertibleDomain r → X ∈ invertibleDomain r) (f : Test) : Test where
  toFun := f ∘ A
  contDiff' := f.contDiff.comp A.toContinuousLinearMap.contDiff
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph A.toHomeomorph
  tsupport_subset' := (tsupport_comp_subset_preimage f A.continuous).trans
    fun _ h => hA _ (f.tsupport_subset h)

/-- Pull a test back by left multiplication by an invertible matrix. -/
def leftTranslateTest (g : G) (f : Test) : Test :=
  pullbackTest (g.mulLeftLinearEquiv ℝ M).toContinuousLinearEquiv (by
    intro X hX
    obtain ⟨h, hh⟩ := hX
    change h.val = g.val * X at hh
    refine ⟨g⁻¹ * h, ?_⟩
    rw [Units.val_mul, hh, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]) f

/-- Pull a test back by right multiplication by an invertible matrix. -/
def rightTranslateTest (g : G) (f : Test) : Test :=
  pullbackTest (g.mulRightLinearEquiv ℝ).toContinuousLinearEquiv (by
    intro X hX
    obtain ⟨h, hh⟩ := hX
    change h.val = X * g.val at hh
    refine ⟨h * g⁻¹, ?_⟩
    rw [Units.val_mul, hh, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]) f

@[simp]
theorem leftTranslateTest_apply (g : G) (f : Test) (X : M) :
    leftTranslateTest g f X = f (g.val * X) := rfl

@[simp]
theorem rightTranslateTest_apply (g : G) (f : Test) (X : M) :
    rightTranslateTest g f X = f (X * g.val) := rfl

/-- Group covariance on the left and right standard upper unipotent subgroups. -/
def IsUnipotentWhittakerCovariant (D : 𝓓'(invertibleDomain r, ℂ)) (a : ℝˣ) : Prop :=
  (∀ (u : U) (f : Test), D (leftTranslateTest u.val f) = D f) ∧
  (∀ (u : U) (f : Test), D (rightTranslateTest u.val f) = realWhittakerCharacter a u.val * D f)

private def entryUnit (ij : I) (t : ℝ) : U :=
  if h : ij.1 < ij.2 then ⟨transvectionUnit ij.1 ij.2 h.ne t, by
    apply (mem_upperUnipotent_iff _ _ _).2
    constructor
    · intro i j hij
      have hn : ¬(ij.1 = i ∧ ij.2 = j) := by
        rintro ⟨rfl, rfl⟩
        exact (not_lt_of_ge h.le) hij
      simp [transvectionUnit, Matrix.transvection, Matrix.one_apply_ne hij.ne', hn]
    · intro i
      have hn : ¬(ij.1 = i ∧ ij.2 = i) := by
        rintro ⟨hi, hj⟩
        exact h.ne (hi.trans hj.symm)
      simp [transvectionUnit, Matrix.transvection, hn]⟩
  else 1

private theorem entryUnit_val (ij : I) (t : ℝ) :
    (entryUnit ij t).val.val = 1 + t • upperEntryDirection ij := by
  by_cases h : ij.1 < ij.2 <;> simp [entryUnit, upperEntryDirection, h, transvectionUnit,
    Matrix.transvection, Matrix.smul_single, smul_eq_mul]

private theorem entryUnit_neg_mul (ij : I) (t : ℝ) :
    (entryUnit ij (-t)).val * (entryUnit ij t).val = 1 := by
  apply Units.ext
  by_cases h : ij.1 < ij.2
  · simp only [entryUnit, dite_eq_left h, transvectionUnit, Units.val_mul, Units.val_one]
    rw [Matrix.transvection_mul_transvection_same _ _ h.ne, neg_add_cancel, Matrix.transvection_zero]
  · simp [entryUnit, h]

private theorem entryUnit_mul_neg (ij : I) (t : ℝ) :
    (entryUnit ij t).val * (entryUnit ij (-t)).val = 1 := by
  simpa only [neg_neg] using entryUnit_neg_mul ij (-t)

private theorem character_entryUnit (a : ℝˣ) (ij : I) (t : ℝ) :
    realWhittakerCharacter a (entryUnit ij t).val =
      (realScaledCharacter a).complex (t * characterWeight (Sum.inr ij)) := by
  simp only [realWhittakerCharacter, entryUnit_val, Matrix.add_apply,
    Matrix.one_apply_ne Fin.castSucc_lt_succ.ne, zero_add, Matrix.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, characterWeight_inr]

private def flow (j : DirectionIndex r) (p : ℝ × M) : M :=
  p.2 + p.1 • ambientField j p.2

private theorem contDiff_flow (j : DirectionIndex r) : ContDiff ℝ ∞ (flow j) :=
  contDiff_snd.add (contDiff_fst.smul ((ambientField j).contDiff.comp contDiff_snd))

private theorem flow_left (ij : I) (t : ℝ) (X : M) :
    flow (Sum.inl ij) (t, X) = (entryUnit ij t).val.val * X := by
  rw [entryUnit_val]
  change X + t • (upperEntryDirection ij * X) = _
  rw [add_mul, one_mul, smul_mul_assoc]

private theorem flow_right (ij : I) (t : ℝ) (X : M) :
    flow (Sum.inr ij) (t, X) = X * (entryUnit ij t).val.val := by
  rw [entryUnit_val]
  change X + t • (X * upperEntryDirection ij) = _
  rw [mul_add, mul_one, mul_smul_comm]

private theorem flow_inverse (j : DirectionIndex r) (t : ℝ) (X : M) :
    flow j (-t, flow j (t, X)) = X := by
  cases j with
  | inl ij =>
    rw [flow_left, flow_left, ← Matrix.mul_assoc, ← Units.val_mul, entryUnit_neg_mul,
      Units.val_one, one_mul]
  | inr ij =>
    rw [flow_right, flow_right, Matrix.mul_assoc, ← Units.val_mul, entryUnit_mul_neg,
      Units.val_one, mul_one]

private theorem flow_mem_invertibleDomain (j : DirectionIndex r) (t : ℝ) {X : M}
    (hX : X ∈ invertibleDomain r) : flow j (t, X) ∈ invertibleDomain r := by
  obtain ⟨g, rfl⟩ := hX
  cases j with
  | inl ij => exact ⟨(entryUnit ij t).val * g, (flow_left ij t g.val).symm⟩
  | inr ij => exact ⟨g * (entryUnit ij t).val, (flow_right ij t g.val).symm⟩

private def timeDomain : Opens ℝ := ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩

private theorem zero_mem_timeDomain : (0 : ℝ) ∈ timeDomain := by
  change (0 : ℝ) ∈ Ioo (-1 : ℝ) 1
  norm_num

private def orbitSupport (j : DirectionIndex r) (f : Test) : Compacts M :=
  ⟨flow j '' (Icc (-1 : ℝ) 1 ×ˢ tsupport f),
    (isCompact_Icc.prod f.hasCompactSupport).image (contDiff_flow j).continuous⟩

private theorem orbitSupport_subset (j : DirectionIndex r) (f : Test) :
    (orbitSupport j f : Set M) ⊆ invertibleDomain r := by
  rintro X ⟨⟨t, Y⟩, ht, rfl⟩
  exact flow_mem_invertibleDomain j t (f.tsupport_subset ht.2)

private theorem family_zero_outside (j : DirectionIndex r) (f : Test) :
    ∀ t ∈ timeDomain, ∀ X ∉ orbitSupport j f, (f ∘ flow j) (t, X) = 0 := by
  intro t ht X hX
  change f (flow j (t, X)) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hn
  have ht' : (-1 : ℝ) < t ∧ t < 1 := ht
  exact hX ⟨(-t, flow j (t, X)), ⟨⟨by linarith [ht'.2], by linarith [ht'.1]⟩, hn⟩,
    flow_inverse j t X⟩

private theorem derivativeFamily_eq (j : DirectionIndex r) (f : Test) :
    (TestFunction.ofSupportedIn (orbitSupport_subset j f)
      (compactTestTimeDerivative (f.contDiff.comp (contDiff_flow j)) zero_mem_timeDomain
        (family_zero_outside j f)) : Test) =
      smoothVectorFieldDerivativeTest (ambientField j).contDiff.contDiffOn f := by
  ext X
  change compactTestTimeDerivative (f.contDiff.comp (contDiff_flow j)) zero_mem_timeDomain
      (family_zero_outside j f) X = fderiv ℝ f X (ambientField j X)
  rw [compactTestTimeDerivative_apply]
  have htime : HasDerivAt (fun t : ℝ => (t, X)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 X)
  have hd := ((f.contDiff.comp (contDiff_flow j)).differentiable (by simp) (0, X)).hasFDerivAt
  have h₁ := hd.comp_hasDerivAt 0 htime
  have h₂ : HasDerivAt (fun t : ℝ => X + t • ambientField j X) (ambientField j X) 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (ambientField j X)).const_add X)
  have h₃ := (f.contDiff.differentiable (by simp) X).hasFDerivAt.comp_hasDerivAt_of_eq 0 h₂
    (by simp : X = X + (0 : ℝ) • ambientField j X)
  exact h₁.unique h₃

/-- The nonzero infinitesimal scalar of the real additive character. -/
def infinitesimalScalar (a : ℝˣ) : ℂ := 2 * π * (a : ℝ) * Complex.I

theorem infinitesimalScalar_ne_zero (a : ℝˣ) : infinitesimalScalar a ≠ 0 := by
  unfold infinitesimalScalar
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Complex.ofReal_ne_zero.mpr a.ne_zero)) Complex.I_ne_zero

/-- Differentiating the real unipotent translation identities gives the
infinitesimal covariance used for Bruhat support descent. -/
theorem infinitesimal_of_unipotent_covariance (D : 𝓓'(invertibleDomain r, ℂ)) (a : ℝˣ)
    (hD : IsUnipotentWhittakerCovariant D a) : IsInfinitesimalWhittakerCovariant D (infinitesimalScalar a) := by
  intro j f
  let T := D.comp (TestFunction.ofSupportedInCLM ℝ (orbitSupport_subset j f))
  let response : ℝ → ℂ := Sum.elim (fun _ _ => D f)
    (fun ij t => (realScaledCharacter a).complex (t * characterWeight (Sum.inr ij)) * D f) j
  have hresponse : HasDerivAt response (infinitesimalScalar a * (characterWeight j • D f)) 0 := by
    cases j with
    | inl ij => simpa [response, characterWeight_inl] using (hasDerivAt_const (0 : ℝ) (D f))
    | inr ij =>
      let q := characterWeight (Sum.inr ij)
      have hq : HasDerivAt (fun t : ℝ => t * q) q 0 := by
        simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const q)
      have hψ := (hasDerivAt_realScaledCharacter a).scomp_of_eq 0 hq
        (by simp : (0 : ℝ) = 0 * q)
      have hc : (q • infinitesimalScalar a) * D f = infinitesimalScalar a * (q • D f) := by
        simp only [Complex.real_smul]
        ring
      change HasDerivAt _ (infinitesimalScalar a * (q • D f)) 0
      rw [← hc]
      exact hψ.mul_const (D f)
  have hT (t : timeDomain) :
      T (compactTestFamily (f.contDiff.comp (contDiff_flow j)) (family_zero_outside j f) t) = response t := by
    cases j with
    | inl ij =>
      have he : (TestFunction.ofSupportedIn (orbitSupport_subset (Sum.inl ij) f)
          (compactTestFamily (f.contDiff.comp (contDiff_flow (Sum.inl ij)))
            (family_zero_outside (Sum.inl ij) f) t) : Test) = leftTranslateTest (entryUnit ij t).val f := by
        ext X
        exact congrArg f (flow_left ij t X)
      change D (TestFunction.ofSupportedIn (orbitSupport_subset (Sum.inl ij) f) _) = D f
      rw [he]
      exact hD.1 _ _
    | inr ij =>
      have he : (TestFunction.ofSupportedIn (orbitSupport_subset (Sum.inr ij) f)
          (compactTestFamily (f.contDiff.comp (contDiff_flow (Sum.inr ij)))
            (family_zero_outside (Sum.inr ij) f) t) : Test) = rightTranslateTest (entryUnit ij t).val f := by
        ext X
        exact congrArg f (flow_right ij t X)
      change D (TestFunction.ofSupportedIn (orbitSupport_subset (Sum.inr ij) f) _) =
        (realScaledCharacter a).complex (t.val * characterWeight (Sum.inr ij)) * D f
      rw [he, hD.2, character_entryUnit]
  have h := eval_compactTestTimeDerivative_of_hasDerivAt (f.contDiff.comp (contDiff_flow j))
    zero_mem_timeDomain (family_zero_outside j f) T response _ hresponse hT
  exact (congrArg D (derivativeFamily_eq j f)).symm.trans h

theorem eq_zero_of_unipotent_covariance_of_reversalCell_vanishing (D : 𝓓'(invertibleDomain r, ℂ))
    (a : ℝˣ) (hD : IsUnipotentWhittakerCovariant D a)
    (hrev : Distribution.IsVanishingOn D (reversalCellImage r)) : D = 0 :=
  eq_zero_of_reversalCell_vanishing D _ (infinitesimalScalar_ne_zero a)
    (infinitesimal_of_unipotent_covariance D a hD) hrev

/-- Full unipotent translation covariance determines a distribution on
invertible real matrices from its restriction to the reversal cell. -/
def RealWhittakerTranslationDistributionStatement : Prop :=
  ∀ (r : ℕ) (D : 𝓓'(invertibleDomain r, ℂ)) (a : ℝˣ), IsUnipotentWhittakerCovariant D a →
    Distribution.IsVanishingOn D (reversalCellImage r) → D = 0

theorem realWhittakerTranslationDistribution : RealWhittakerTranslationDistributionStatement :=
  fun _ => eq_zero_of_unipotent_covariance_of_reversalCell_vanishing

end Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslationDistribution
