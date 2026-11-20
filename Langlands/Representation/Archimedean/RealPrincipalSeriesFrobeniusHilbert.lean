import Langlands.Representation.Archimedean.RealPrincipalSeriesAnalytic
import Langlands.Representation.Archimedean.RealPrincipalSeriesHilbertAction

/-! # Genuine Hilbert orbits of real Frobenius vectors -/

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

attribute [local instance 100] LieRing.ofAssociativeRing

open RealJacquetFrobenius RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK borelSpaceK

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "I" => matrixModel ℝ n
local notation "K" => unitaryCompact ℝ n

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

private theorem frobenius_sign (h : IsRealJacquetFunctional n ρ π ℓ a e) (j : Fin n) (v : V) :
    ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v := (h.2 j v).2

/-- The real Jacquet Frobenius map, with codomain the full smooth principal series. -/
def frobeniusPrincipalSeries : V →ₗ[ℂ] PrincipalSeries a e :=
  (frobLin ρ ℓ a e).codRestrict _ fun v =>
    (mem_principalSeries_iff ℝ n _ _).mpr
      ⟨contMDiff_frobFun (frobenius_sign hℓ) hgk.1 hgk.2.1 v, frobFun_left (frobenius_sign hℓ) v⟩

/-- The Frobenius map into the compact Hilbert completion. -/
def frobeniusHilbert : V →ₗ[ℂ] Hilbert a e :=
  (embed a e).comp (frobeniusPrincipalSeries hgk hℓ)

@[simp]
theorem representation_frobeniusHilbert_compact (k : K) (v : V) :
    representation a e (k : GL) (frobeniusHilbert hgk hℓ v) =
      frobeniusHilbert hgk hℓ (ρ ⟨((k : GL) : Mat), k.2⟩ v) := by
  change representation a e (k : GL) (embed a e (frobeniusPrincipalSeries hgk hℓ v)) = _
  rw [representation_embed]
  apply congrArg (embed a e)
  apply Subtype.ext
  exact (frobFun_rightTranslation (frobenius_sign hℓ) k v).symm

private def toHilbert : C(K, ℂ) →L[ℂ] Hilbert a e :=
  (closureSubmodule a e).orthogonalProjectionOnto.comp (ContinuousMap.toLp 2 (haarK n) ℂ)

private theorem toHilbert_compactRestriction (f : PrincipalSeries a e) :
    toHilbert (compactRestriction a e f) = embed a e f := by
  change (closureSubmodule a e).orthogonalProjectionOnto (restrictToL2 a e f) = embed a e f
  rw [← coe_embed]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (embed a e f)

private theorem exists_analyticAt_compactOrbit_frobenius (v : V) :
    ∃ T : Mat → C(K, ℂ), AnalyticAt ℝ T 1 ∧
      ∀ᶠ A in 𝓝 (1 : Mat), ∀ g : GL, (g : Mat) = A →
        T A = compactRestriction a e (translation a e g (frobeniusPrincipalSeries hgk hℓ v)) := by
  obtain ⟨P, hP⟩ := exists_polyEval (ℓ := ℓ) hgk.1 hgk.2.1 v
  obtain ⟨T, hT, hEq⟩ := exists_analyticAt_compactOrbit_frobFun (frobenius_sign hℓ) v hP
  refine ⟨T, hT, ?_⟩
  filter_upwards [hEq] with A hA g hg
  exact ContinuousMap.ext (hA g hg)

private theorem exists_analyticAt_hilbertOrbit_frobenius (v : V) :
    ∃ S : Mat → Hilbert a e, AnalyticAt ℝ S 1 ∧
      ∀ᶠ A in 𝓝 (1 : Mat), ∀ g : GL, (g : Mat) = A →
        S A = representation a e g (frobeniusHilbert hgk hℓ v) := by
  obtain ⟨T, hT, hEq⟩ := exists_analyticAt_compactOrbit_frobenius hgk hℓ v
  let Q := (toHilbert (a := a) (e := e)).restrictScalars ℝ
  refine ⟨toHilbert ∘ T, (Q.analyticAt (T 1)).comp hT, ?_⟩
  filter_upwards [hEq] with A hA g hg
  simp only [Function.comp_apply, hA g hg, toHilbert_compactRestriction, frobeniusHilbert,
    LinearMap.comp_apply, representation_embed]

/-- Every Frobenius vector is smooth for the genuine Hilbert action. -/
theorem isSmoothVector_frobeniusHilbert (v : V) :
    IsSmoothVector I (representation a e) (frobeniusHilbert hgk hℓ v) := by
  obtain ⟨S, hS, hS_eq⟩ := exists_analyticAt_hilbertOrbit_frobenius hgk hℓ v
  intro g₀
  have hmul : ContMDiffAt I I ∞ (fun g : GL => g₀⁻¹ * g) g₀ :=
    (contMDiff_const.mul contMDiff_id).contMDiffAt
  have hchart : ContMDiffAt I 𝓘(ℝ, Mat) ∞ (fun g : GL => ((g₀⁻¹ * g : GL) : Mat)) g₀ :=
    Units.contMDiff_val.contMDiffAt.comp g₀ hmul
  have hlocal : ContMDiffAt 𝓘(ℝ, Mat) 𝓘(ℝ, Hilbert a e) ∞ S ((g₀⁻¹ * g₀ : GL) : Mat) := by
    simpa only [inv_mul_cancel, Units.val_one] using hS.contDiffAt.contMDiffAt
  let A := (representation a e g₀).restrictScalars ℝ
  have hA : ContMDiff 𝓘(ℝ, Hilbert a e) 𝓘(ℝ, Hilbert a e) ∞ A := A.contDiff.contMDiff
  apply (hA.contMDiffAt.comp g₀ (hlocal.comp g₀ hchart)).congr_of_eventuallyEq
  have ht : Tendsto (fun g : GL => ((g₀⁻¹ * g : GL) : Mat)) (𝓝 g₀) (𝓝 1) := by
    simpa only [inv_mul_cancel, Units.val_one] using hchart.continuousAt.tendsto
  filter_upwards [ht.eventually hS_eq] with g hg
  change representation a e g (frobeniusHilbert hgk hℓ v) =
    representation a e g₀ (S ((g₀⁻¹ * g : GL) : Mat))
  rw [hg (g₀⁻¹ * g) rfl, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

private theorem analyticAt_exp_smul_zero (X : Mat) :
    AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) 0 :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp (((1 : ℝ →L[ℝ] ℝ).smulRight X).analyticAt 0)

private theorem tendsto_exp_smul_zero (X : Mat) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • X)) (𝓝 0) (𝓝 (1 : Mat)) := by
  simpa only [zero_smul, NormedSpace.exp_zero] using (analyticAt_exp_smul_zero X).continuousAt.tendsto

private theorem analyticAt_exponential_frobeniusHilbert_zero (X : Mat) (v : V) :
    AnalyticAt ℝ (fun t : ℝ => representation a e (matrixExpUnit n (t • X))
      (frobeniusHilbert hgk hℓ v)) 0 := by
  obtain ⟨S, hS, hS_eq⟩ := exists_analyticAt_hilbertOrbit_frobenius hgk hℓ v
  have h : AnalyticAt ℝ S (NormedSpace.exp ((0 : ℝ) • X)) := by simpa using hS
  apply (h.comp (f := fun t : ℝ => NormedSpace.exp (t • X)) (analyticAt_exp_smul_zero X)).congr
  filter_upwards [(tendsto_exp_smul_zero X).eventually hS_eq] with t ht
  exact ht (matrixExpUnit n (t • X)) rfl

/-- The Hilbert orbit of a Frobenius vector along a matrix exponential is real analytic. -/
theorem analyticAt_exponential_frobeniusHilbert (X : Mat) (v : V) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => representation a e (matrixExpUnit n (s • X))
      (frobeniusHilbert hgk hℓ v)) t := by
  let T : ℝ → Hilbert a e := fun s => representation a e (matrixExpUnit n (s • X))
    (frobeniusHilbert hgk hℓ v)
  let A := (representation a e (matrixExpUnit n (t • X))).restrictScalars ℝ
  have hT : AnalyticAt ℝ T (t - t) := by
    rw [sub_self]
    exact analyticAt_exponential_frobeniusHilbert_zero hgk hℓ X v
  have hshift : AnalyticAt ℝ (fun s : ℝ => s - t) t := analyticAt_id.sub analyticAt_const
  have h : AnalyticAt ℝ (fun s => A (T (s - t))) t :=
    (A.analyticAt _).comp (hT.comp (f := fun s : ℝ => s - t) hshift)
  apply h.congr (Eventually.of_forall fun s => ?_)
  change representation a e (matrixExpUnit n (t • X)) (representation a e
    (matrixExpUnit n ((s - t) • X)) (frobeniusHilbert hgk hℓ v)) = _
  rw [← mul_apply_eq_comp, ← map_mul, ← matrixExpUnit_add_smul,
    show t + (s - t) = s by ring]

/-- The derivative of the actual Hilbert orbit along a matrix exponential at the identity
is the Frobenius image of the given real Lie action. -/
theorem hasDerivAt_exponential_frobeniusHilbert_zero (X : Mat) (v : V) :
    HasDerivAt (fun t : ℝ => representation a e (matrixExpUnit n (t • X))
      (frobeniusHilbert hgk hℓ v)) (frobeniusHilbert hgk hℓ (π (1 ⊗ₜ X) v)) 0 := by
  obtain ⟨T, hT, hEq⟩ := exists_analyticAt_compactOrbit_frobenius hgk hℓ v
  let P : ℝ → C(K, ℂ) := fun t => T (NormedSpace.exp (t • X))
  have hTA : AnalyticAt ℝ T (NormedSpace.exp ((0 : ℝ) • X)) := by simpa using hT
  have hP : AnalyticAt ℝ P 0 :=
    hTA.comp (f := fun t : ℝ => NormedSpace.exp (t • X)) (analyticAt_exp_smul_zero X)
  have hD := hP.hasStrictDerivAt.hasDerivAt
  let f := frobeniusPrincipalSeries hgk hℓ (π (1 ⊗ₜ X) v)
  have hcurve : ∀ᶠ t in 𝓝 (0 : ℝ), P t =
      compactRestriction a e (translation a e (matrixExpUnit n (t • X))
        (frobeniusPrincipalSeries hgk hℓ v)) := by
    filter_upwards [(tendsto_exp_smul_zero X).eventually hEq] with t ht
    exact ht (matrixExpUnit n (t • X)) rfl
  have hderiv : deriv P 0 = compactRestriction a e f := by
    apply ContinuousMap.ext
    intro k
    have hd := (ContinuousMap.evalCLM ℝ (M := ℂ) k).hasFDerivAt.comp_hasDerivAt 0 hD
    have hs := hasDerivAt_mul_matrixExpUnit_smul
      ((frobeniusPrincipalSeries hgk hℓ v).2.1.of_le (by simp)) (k : GL) X
    have hs' : HasDerivAt (fun t : ℝ => frobFun ρ ℓ a e v ((k : GL) * matrixExpUnit n (t • X)))
        (compactRestriction a e f k) 0 := by
      change HasDerivAt (fun t : ℝ => frobFun ρ ℓ a e v ((k : GL) * matrixExpUnit n (t • X)))
        (frobFun ρ ℓ a e (π (1 ⊗ₜ X) v) (k : GL)) 0
      rw [frobFun_rightDerivative hgk hℓ]
      exact hs
    apply hd.unique
    exact hs'.congr_of_eventuallyEq (hcurve.mono fun t ht => congrArg (fun c : C(K, ℂ) => c k) ht)
  rw [hderiv] at hD
  have h := ((toHilbert (a := a) (e := e)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hD
  change HasDerivAt (fun t => toHilbert (P t)) (toHilbert (compactRestriction a e f)) 0 at h
  rw [toHilbert_compactRestriction] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hcurve] with t ht
  rw [ht, toHilbert_compactRestriction, frobeniusHilbert, LinearMap.comp_apply, representation_embed]

private theorem hasDerivAt_exponentialOrbit_zero {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (R : GL →* (H →L[ℂ] H))
    (X : Mat) {v : H} (hv : IsSmoothVector I R v) :
    HasDerivAt (fun t : ℝ => R (matrixExpUnit n (t • X)) v) (lieDerivative I R X v) 0 := by
  have hc := hasMFDerivAt_matrixExpUnit_smul n X
  have hd := hv.mdifferentiableAt (x := (1 : GL)) (by simp)
  have h₀ : matrixExpUnit n ((0 : ℝ) • X) = 1 := by rw [zero_smul, matrixExpUnit_zero]
  let A := mfderiv I 𝓘(ℝ, H) (orbitMap R v) 1
  have hF : HasMFDerivAt I 𝓘(ℝ, H) (orbitMap R v) (matrixExpUnit n ((0 : ℝ) • X)) A := by
    rw [h₀]
    exact hd.hasMFDerivAt
  have h := HasMFDerivAt.comp (f := fun t : ℝ => matrixExpUnit n (t • X)) 0 hF hc
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have hA : (A.comp ((1 : ℝ →L[ℝ] ℝ).smulRight X)) 1 = A X := by simp
  exact h.hasDerivAt.congr_deriv hA

/-- Genuine differentiation at the identity realizes the given GK Lie action. -/
theorem lieDerivative_frobeniusHilbert (X : Mat) (v : V) :
    lieDerivative I (representation a e) X (frobeniusHilbert hgk hℓ v) =
      frobeniusHilbert hgk hℓ (π (1 ⊗ₜ X) v) :=
  (hasDerivAt_exponentialOrbit_zero (representation a e) X
    (isSmoothVector_frobeniusHilbert hgk hℓ v)).unique
      (hasDerivAt_exponential_frobeniusHilbert_zero hgk hℓ X v)

end Langlands.Archimedean.RealPrincipalSeriesHilbert
