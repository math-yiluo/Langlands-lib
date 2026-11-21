import Langlands.HarmonicAnalysis.Distribution.AffineConjugationDistribution
import Langlands.HarmonicAnalysis.Distribution.ConormalCoefficientTests
import Langlands.HarmonicAnalysis.Distribution.RealSpectralOrbitJacobian
import Langlands.HarmonicAnalysis.Distribution.ZeroNormalChartCovariance
import Langlands.LinearAlgebra.MatrixTransposeConjugateProof
import Langlands.LinearAlgebra.RealSpectralLocalAction

/-! # Vanishing of a transpose-odd distribution on a real spectral chart -/

noncomputable section

open Filter Function Matrix MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
  {W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} {N : Submodule ℝ W}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A
local notation "Coord" => ((T[A] × Z[A]) × N)

variable {e : OpenPartialHomeomorph
    (((LinearMap.range (matrixConjugationTangent A)) × realMatrixSemisimpleDirections A) × N)
    (Matrix (Fin n) (Fin n) ℝ)}
  (J : (LinearMap.range (matrixConjugationTangent A)) →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
  (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
  (hformula : ∀ p, e p = (1 + J p.1.1) *
    (A + (p.1.2 : Matrix (Fin n) (Fin n) ℝ) + ((p.2 : W) : Matrix (Fin n) (Fin n) ℝ)) *
      Ring.inverse (1 + J p.1.1))
  (hunit : ∀ p ∈ e.source, IsUnit (1 + J p.1.1))
  (L : (((LinearMap.range (matrixConjugationTangent A)) × realMatrixSemisimpleDirections A) × N) ≃L[ℝ]
    Matrix (Fin n) (Fin n) ℝ)
  {Q : Opens (LinearMap.range (matrixConjugationTangent A))}
  {U : Opens (realMatrixSemisimpleDirections A)} {V : Opens N}

local notation "Domain" => productTestDomain (productTestDomain Q U) V

variable (hΩ : productTestDomain (productTestDomain Q U) V ≤ chartSource e) (D : FullDistribution n)
  (hconj : IsFullConjugationInvariant D)
  (hZW : realMatrixSemisimpleDirections A ≤ W)
  (hTW : IsCompl (LinearMap.range (matrixConjugationTangent A)) W)
  (hN : IsCompl ((realMatrixSemisimpleDirections A).comap W.subtype) N)

/-- The leading coefficient on the semisimple slice of a normalized spectral chart. -/
def realSpectralOrbitCoefficient (χ : 𝓓(Q, ℝ)) (ζ : 𝓓(V, ℝ)) (i : ℕ) :
    𝓓(U, (↥N) [×i]→L[ℝ] ℝ) →L[ℝ] ℂ :=
  transverseProductJetCoefficient
    (orbitSliceDistribution (jacobianNormalizedChartDistribution he hei L hΩ D) χ) ζ i

include hformula hunit hconj in
private theorem eval_normalizedChart_orbitDerivative_eq_zero (v : T[A]) (f : 𝓓(Domain, ℝ)) :
    jacobianNormalizedChartDistribution he hei L hΩ D (TestFunction.lineDerivCLM ℝ ((v, 0), 0) f) = 0 := by
  let J' : Coord →L[ℝ] Mat := J.comp ((ContinuousLinearMap.fst ℝ T[A] Z[A]).comp
    (ContinuousLinearMap.fst ℝ (T[A] × Z[A]) N))
  let B' : Coord →L[ℝ] Mat :=
    Z[A].subtypeL.comp ((ContinuousLinearMap.snd ℝ T[A] Z[A]).comp
      (ContinuousLinearMap.fst ℝ (T[A] × Z[A]) N)) +
    (W.subtypeL.comp N.subtypeL).comp (ContinuousLinearMap.snd ℝ (T[A] × Z[A]) N)
  let B (p : Coord) : Mat := A + B' p
  have hB : ContDiff ℝ ∞ B := contDiff_const.add B'.contDiff
  have hB'd (p : Coord) : fderiv ℝ B p = B' := (B'.hasFDerivAt (x := p)).const_add A |>.fderiv
  have hderiv : TestFunction.lineDerivCLM ℝ ((v, 0), 0) f =
      smoothVectorFieldDerivativeTest (contDiffOn_const (c := ((v, 0), 0))) f := by
    ext x
    rw [lineDerivCLM_smoothTest_apply, smoothVectorFieldDerivativeTest_apply]
  rw [hderiv]
  refine eval_jacobianNormalizedChartDistribution_affineOrbitDerivative_eq_zero he hei L hΩ
    D hconj J' hB.contDiffOn (fun p hp => hunit p (hΩ hp)) ?_ ((v, 0), 0) ?_ f
  · intro p _
    rw [hformula]
    change (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) * Ring.inverse (1 + J p.1.1) =
      (1 + J p.1.1) * (A + ((p.1.2 : Mat) + ((p.2 : W) : Mat))) * Ring.inverse (1 + J p.1.1)
    rw [add_assoc]
  · intro p _
    rw [hB'd]
    change ((0 : Z[A]) : Mat) + (((0 : N) : W) : Mat) = 0
    simp

private theorem pureCovectorPowerTest_symmetric (i : ℕ) (f : 𝓓(U, ℝ)) (l : N →L[ℝ] ℝ)
    (z : Z[A]) (v : Fin i → N) (σ : Equiv.Perm (Fin i)) :
    pureCovectorPowerTest i f l z (v ∘ σ) = pureCovectorPowerTest i f l z v := by
  simp only [pureCovectorPowerTest_apply, _root_.smul_apply, continuousCovectorPower_apply]
  congr 1
  exact Equiv.prod_comp σ (fun k => l (v k))

private theorem pureCovectorPowerTest_postcomp (i : ℕ) (f : 𝓓(U, ℝ)) (l : N →L[ℝ] ℝ)
    (M : N →L[ℝ] N) :
    TestFunction.postcompCLM (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => M))
      (pureCovectorPowerTest i f l) = pureCovectorPowerTest i f (l.comp M) := by
  apply TestFunction.ext
  intro z
  simp only [TestFunction.postcompCLM_apply, Function.comp_apply, pureCovectorPowerTest_apply, map_smul]
  change f z • (continuousCovectorPower i l).compContinuousLinearMap (fun _ => M) = _
  rw [continuousCovectorPower_comp]

variable {R : Set (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)} (hR : IsOpen R)
  (hrec : ∀ (z : realMatrixSemisimpleDirections A) (B : Matrix (Fin n) (Fin n) ℝ),
    (A + (z : Matrix (Fin n) (Fin n) ℝ), B) ∈ R →
    (∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ, u.val * (A + (z : Matrix (Fin n) (Fin n) ℝ)) = B * u.val) →
    B ∈ e.target ∧ (e.symm B).1.2 = z ∧ (e.symm B).2 = 0)
  (hdiag : ∀ z ∈ U, (A + (z : Matrix (Fin n) (Fin n) ℝ), A + (z : Matrix (Fin n) (Fin n) ℝ)) ∈ R)
  (hTangent : ∀ z ∈ U, LinearMap.range (matrixConjugationTangent (A + (z : Matrix (Fin n) (Fin n) ℝ))) =
    LinearMap.range (matrixConjugationTangent A))
  (hQ : (0 : LinearMap.range (matrixConjugationTangent A)) ∈ Q) (hV : (0 : N) ∈ V)

include hΩ hQ hV in
private theorem spectralSlice_source {z : Z[A]} (hz : z ∈ U) : ((0, z), 0) ∈ e.source :=
  hΩ ⟨⟨hQ, hz⟩, hV⟩

include hformula hunit hrec hdiag hR hTangent hQ hV in
private theorem realSpectralOrbitCoefficient_covariant
    [MeasurableSpace T[A]] [BorelSpace T[A]] (μ : Measure T[A]) [μ.IsAddHaarMeasure]
    (χ : 𝓓(Q, ℝ)) (hχ : (∫ t, χ t ∂μ) = 1)
    (hFactor : ∀ f : 𝓓(Domain, ℝ), jacobianNormalizedChartDistribution he hei L hΩ D f =
      orbitSliceDistribution (jacobianNormalizedChartDistribution he hei L hΩ D) χ (orbitIntegratedTest μ f))
    (i : ℕ) (hord : HasTransverseJetOrder (orbitSliceDistribution
      (jacobianNormalizedChartDistribution he hei L hΩ D) χ) i)
    (ζ : 𝓓(V, ℝ)) (hζ : (ζ : N → ℝ) =ᶠ[𝓝 0] 1)
    (P : Mat ≃L[ℝ] Mat) (hP : |P.toContinuousLinearMap.det| = 1)
    (hPs : ∀ z : Z[A], P (A + (z : Mat)) = A + (z : Mat))
    (hSim : ∀ (u : Matˣ) (B : Mat), ∃ v : Matˣ, v.val * P B = P (u.val * B * u.inv) * v.val)
    (hSim' : ∀ (u : Matˣ) (B : Mat), ∃ v : Matˣ, v.val * P.symm B = P.symm (u.val * B * u.inv) * v.val)
    (hJ : ∀ z ∈ U, zeroNormalOrbitJacobian (chartLinearTransition e P) (0, z) = 1)
    (c : ℝ) (hD : ∀ f : FullTest n, D (fullSmoothTestPullbackCLM P f) = c • D f)
    (f : 𝓓(U, ℝ)) (l : N →L[ℝ] ℝ) :
    let C := realSpectralOrbitCoefficient he hei L hΩ D χ ζ i
    C (pureCovectorPowerTest i f (l.comp (realMatrixStratumNormalAction hZW hTW hN P.toContinuousLinearMap))) =
      c • C (pureCovectorPowerTest i f l) := by
  let Ψ := chartLinearTransition e P
  let M := realMatrixStratumNormalAction hZW hTW hN P.toContinuousLinearMap
  let a := pureCovectorPowerTest i f l
  have hz (z : Z[A]) (hz' : z ∈ tsupport a) : ((0, z), 0) ∈ e.source :=
    spectralSlice_source hΩ hQ hV (a.tsupport_subset hz')
  have hfix (z : Z[A]) (h : z ∈ tsupport a) :
      ((0, z), 0) ∈ Ψ.source ∧ Ψ ((0, z), 0) = ((0, z), 0) :=
    realMatrixChartAction_slice_fixed J e hformula P z (hz z h) (hPs z)
  have hNDeriv (z : Z[A]) (h : z ∈ tsupport a) : productNormalDerivative Ψ (0, z) = M := by
    let j (y : N) : Coord := ((0, z), y)
    have hj : HasFDerivAt j (ContinuousLinearMap.inr ℝ (T[A] × Z[A]) N) 0 := by
      refine ((hasFDerivAt_const (𝕜 := ℝ) ((0 : T[A]), z) (0 : N)).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) (0 : N))).congr_fderiv ?_
      ext1 v
      rfl
    have hd := ((contDiffOn_chartLinearTransition he hei P).contDiffAt
      (Ψ.open_source.mem_nhds (hfix z h).1)).differentiableAt (by simp)
    have hderiv : HasFDerivAt (fun y : N => (Ψ (j y)).2) (productNormalDerivative Ψ (0, z)) 0 :=
      (hd.hasFDerivAt.comp 0 hj).snd
    exact hderiv.unique (hasFDerivAt_realMatrixStratumChartAction_normal hZW hTW hN J e
      hformula hei z (hz z h) (hTangent z (a.tsupport_subset h)) P.toContinuousLinearMap (hPs z))
  have hPs' (z : Z[A]) : P.symm (A + (z : Mat)) = A + (z : Mat) :=
    P.symm_apply_eq.mpr (hPs z).symm
  have h := orbitSliceCoefficient_eq_of_chartLinearTransition he hei L D μ hΩ P hP c hD χ hχ hFactor
    hQ hV i hord ζ hζ a (pureCovectorPowerTest_symmetric i f l) M hfix ?_ ?_
    (fun z hz' => hJ z (a.tsupport_subset hz')) hNDeriv
  · change realSpectralOrbitCoefficient he hei L hΩ D χ ζ i
        (TestFunction.postcompCLM (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => M))
          (pureCovectorPowerTest i f l)) = _ at h
    rwa [pureCovectorPowerTest_postcomp] at h
  · intro z hza
    filter_upwards [eventually_realMatrixChartAction_preserves_plane J e R hformula hunit hR hrec
      P hSim hPs z (hz z hza) (hdiag z (a.tsupport_subset hza))] with p hp
    exact Prod.ext (Prod.ext rfl hp.2.1) hp.2.2
  · intro z hza
    filter_upwards [eventually_realMatrixChartAction_preserves_plane J e R hformula hunit hR hrec
      P.symm hSim' hPs' z (hz z hza) (hdiag z (a.tsupport_subset hza))] with p hp
    exact Prod.ext (Prod.ext rfl hp.2.1) hp.2.2

private def transposeUnit (u : Matˣ) : Matˣ where
  val := u.valᵀ
  inv := u.invᵀ
  val_inv := by rw [← transpose_mul, u.inv_val, transpose_one]
  inv_val := by rw [← transpose_mul, u.val_inv, transpose_one]

private theorem fullAdjustedTransposeEquiv_symm (q : Matˣ) :
    (fullAdjustedTransposeEquiv q).symm = fullAdjustedTransposeEquiv (transposeUnit q) := by
  apply ContinuousLinearEquiv.ext
  funext X
  apply (fullAdjustedTransposeEquiv q).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change X = q.inv * (q.invᵀ * Xᵀ * q.valᵀ)ᵀ * q.val
  simp [transpose_mul, mul_assoc]

include hformula hunit hconj hZW hTW hN hrec hdiag hR hTangent hQ hV in
/-- The normalized product restriction of a conjugation-invariant and
transpose-odd distribution is zero on a spectral chart of finite transverse order. -/
theorem normalizedProductChartDistribution_eq_zero_of_realSpectralChart
    (hodd : IsFullTransposeAntiInvariant D)
    {d : ℕ} (b : (Fin d → ℝ) ≃L[ℝ] T[A]) {a c : ℝ} (hac : a < c)
    (hbox : b ⁻¹' (Q : Set T[A]) = openIntervalBox d a c)
    (j : ℕ) (hord : HasTransverseJetOrder (jacobianNormalizedChartDistribution he hei L hΩ D) j) :
    jacobianNormalizedChartDistribution he hei L hΩ D = 0 := by
  let _ : MeasurableSpace T[A] := borel T[A]
  let _ : BorelSpace T[A] := ⟨rfl⟩
  let μ := orbitCoordinateMeasure b
  obtain ⟨χ, _, hχ⟩ := exists_normalized_smoothTest μ hQ
  obtain ⟨ζ, hζ⟩ := exists_test_eq_one_near_zero hV
  obtain ⟨q, hq⟩ := matrixTransposeConjugate ℝ n A
  let T := jacobianNormalizedChartDistribution he hei L hΩ D
  let S := orbitSliceDistribution T χ
  have hFactor (f : 𝓓(Domain, ℝ)) : T f = S (orbitIntegratedTest μ f) :=
    eval_eq_orbitSliceDistribution b hac hbox T
      (eval_normalizedChart_orbitDerivative_eq_zero J he hei hformula hunit L hΩ D hconj) χ hχ f
  have hcoeff (i : ℕ) (hi : HasTransverseJetOrder S i) (a' : 𝓓(U, (↥N) [×i]→L[ℝ] ℝ))
      (ha' : ∀ z v (σ : Equiv.Perm (Fin i)), a' z (v ∘ σ) = a' z v) :
      transverseProductJetCoefficient S ζ i a' = 0 := by
    apply realMatrixStratum_symmetricCoefficient_eq_zero hZW hTW hN
      (realSpectralOrbitCoefficient he hei L hΩ D χ ζ i) hq _ _ a' ha'
    · intro u hu f l
      have hP : |(fullConjugationEquiv u).toContinuousLinearMap.det| = 1 := by
        rw [det_fullConjugationEquiv, abs_one]
      have hs (z : Z[A]) : fullConjugationEquiv u (A + (z : Mat)) = A + (z : Mat) :=
        conjugate_add_semisimpleDirection_eq hu z.property
      have hd (g : FullTest n) : D (fullSmoothTestPullbackCLM (fullConjugationEquiv u) g) = (1 : ℝ) • D g := by
        rw [fullSmoothTestPullbackCLM_fullConjugation, hconj, one_smul]
      have hsymm : (fullConjugationEquiv u).symm = fullConjugationEquiv u⁻¹ := by
        apply ContinuousLinearEquiv.ext
        funext X
        exact congrArg (fun t : Mat ≃ₗ[ℝ] Mat => t X) (matrixConjugationLinearEquiv_symm u)
      have h := realSpectralOrbitCoefficient_covariant J he hei hformula hunit L hΩ D hZW hTW hN hR hrec
        hdiag hTangent hQ hV μ χ hχ hFactor i hi ζ hζ (fullConjugationEquiv u) hP hs
        (exists_intertwiner_matrixConjugationLinearEquiv u)
        (by rw [hsymm]; exact exists_intertwiner_matrixConjugationLinearEquiv u⁻¹)
        (fun z hz => zeroNormalOrbitJacobian_realSpectralConjugation J hformula he hei z
          (spectralSlice_source hΩ hQ hV hz) (hTangent z hz) hu) 1 hd f l
      simpa only [one_smul, realMatrixStratumStabilizerNormalAction, matrixConjugationLinearEquiv] using h
    · intro f l
      have hs (z : Z[A]) : fullAdjustedTransposeEquiv q (A + (z : Mat)) = A + (z : Mat) :=
        adjustedTranspose_add_semisimpleDirection_eq hq z.property
      have hd (g : FullTest n) : D (fullSmoothTestPullbackCLM (fullAdjustedTransposeEquiv q) g) =
          (-1 : ℝ) • D g := by
        rw [eval_fullSmoothTestPullbackCLM_fullAdjustedTranspose D hconj hodd, neg_one_smul]
      have h := realSpectralOrbitCoefficient_covariant J he hei hformula hunit L hΩ D hZW hTW hN hR hrec
        hdiag hTangent hQ hV μ χ hχ hFactor i hi ζ hζ (fullAdjustedTransposeEquiv q)
        (abs_det_fullAdjustedTransposeEquiv q) hs (exists_intertwiner_matrixAdjustedTransposeLinearEquiv q)
        (by rw [fullAdjustedTransposeEquiv_symm]; exact exists_intertwiner_matrixAdjustedTransposeLinearEquiv _)
        (fun z hz => zeroNormalOrbitJacobian_realSpectralAdjustedTranspose J hformula he hei z
          (spectralSlice_source hΩ hQ hV hz) (hTangent z hz) hq) (-1) hd f l
      simpa only [neg_one_smul, realMatrixStratumAdjustedTransposeNormalAction] using h
  have heval (i : ℕ) (hi : HasTransverseJetOrder S i) (f : 𝓓(productTestDomain U V, ℝ))
      (hf : ∀ k < i, transverseProductJetCLM k f = 0) : S f = 0 := by
    rw [eval_eq_transverseProductJetCoefficient_of_lower_eq_zero S i hi ζ hζ f hf]
    exact hcoeff i hi _ (transverseProductJetCLM_comp_perm i f)
  have hzero (i : ℕ) : HasTransverseJetOrder S i → S = 0 := by
    induction i with
    | zero =>
      intro hi
      ext f
      exact heval 0 hi f (fun k hk => (Nat.not_lt_zero k hk).elim)
    | succ i ih =>
      intro hi
      apply ih
      intro f hf
      exact heval (i + 1) hi f (fun k hk => hf k (Nat.le_of_lt_succ hk))
  have hS : S = 0 := hzero j (hasTransverseJetOrder_orbitSliceDistribution T χ hord)
  ext f
  change T f = 0
  rw [hFactor, hS]
  rfl

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
