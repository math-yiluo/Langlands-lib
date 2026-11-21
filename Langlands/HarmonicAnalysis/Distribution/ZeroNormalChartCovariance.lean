import Langlands.HarmonicAnalysis.Distribution.OrbitCoefficientCovariance
import Langlands.HarmonicAnalysis.Distribution.WeightedChartTransition

/-! # Local weighted covariance on zero-normal chart fibers -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {O Z N : Type*} [NormedAddCommGroup O] [NormedAddCommGroup Z] [NormedAddCommGroup N]

local notation "Coord" => ((O × Z) × N)

private abbrev preservesFiberAt (Ψ : OpenPartialHomeomorph Coord Coord) (p : O × Z) : Prop :=
  Ψ (p, 0) = (((Ψ (p, 0)).1.1, p.2), 0)

private def zeroNormalFiberOpen (Ψ : OpenPartialHomeomorph Coord Coord) : Opens Coord :=
  ⟨Prod.fst ⁻¹' interior {p | preservesFiberAt Ψ p}, isOpen_interior.preimage continuous_fst⟩

/-- Restrict the source to the fixed product and to open regions where the
transition and its inverse preserve each zero-normal fiber. -/
def zeroNormalFiberTransitionSource (Ψ : OpenPartialHomeomorph Coord Coord) (Ω : Opens Coord) :
    Opens Coord :=
  (Ω ⊓ zeroNormalFiberOpen Ψ) ⊓
    ⟨Ψ.source ∩ Ψ ⁻¹' (Ω ⊓ zeroNormalFiberOpen Ψ.symm : Opens Coord),
      Ψ.isOpen_inter_preimage (Ω ⊓ zeroNormalFiberOpen Ψ.symm).isOpen⟩

/-- The restriction keeps the transition and inverse functions. -/
abbrev zeroNormalFiberTransitionOn (Ψ : OpenPartialHomeomorph Coord Coord) (Ω : Opens Coord) :=
  Ψ.restrOpen (zeroNormalFiberTransitionSource Ψ Ω) (zeroNormalFiberTransitionSource Ψ Ω).isOpen

theorem zeroNormalFiberTransitionSource_le (Ψ : OpenPartialHomeomorph Coord Coord) (Ω : Opens Coord) :
    zeroNormalFiberTransitionSource Ψ Ω ≤ chartSource Ψ := fun _ hx => hx.2.1

theorem zeroNormalFiberTransitionSource_le_domain (Ψ : OpenPartialHomeomorph Coord Coord) (Ω : Opens Coord) :
    zeroNormalFiberTransitionSource Ψ Ω ≤ Ω := fun _ hx => hx.1.1

@[simp]
theorem zeroNormalFiberTransitionOn_source (Ψ : OpenPartialHomeomorph Coord Coord) (Ω : Opens Coord) :
    (zeroNormalFiberTransitionOn Ψ Ω).source = zeroNormalFiberTransitionSource Ψ Ω := by
  rw [zeroNormalFiberTransitionOn, OpenPartialHomeomorph.restrOpen_source]
  exact inter_eq_right.mpr (zeroNormalFiberTransitionSource_le Ψ Ω)

theorem mem_zeroNormalFiberTransitionOn_target_forward
    {Ψ : OpenPartialHomeomorph Coord Coord} {Ω : Opens Coord} {x : Coord}
    (hx : x ∈ (zeroNormalFiberTransitionOn Ψ Ω).target) : x ∈ Ω ∧ x ∈ zeroNormalFiberOpen Ψ.symm := by
  let Ψ' := zeroNormalFiberTransitionOn Ψ Ω
  have h := Ψ'.map_target hx
  rw [zeroNormalFiberTransitionOn_source] at h
  have hs : Ψ (Ψ.symm x) ∈ Ω ⊓ zeroNormalFiberOpen Ψ.symm := h.2.2
  rwa [Ψ.right_inv (show x ∈ Ψ.target from hx.1)] at hs

theorem preservesZeroNormalFibers_zeroNormalFiberTransitionOn (Ψ : OpenPartialHomeomorph Coord Coord)
    (Ω : Opens Coord) : PreservesZeroNormalFibers (zeroNormalFiberTransitionOn Ψ Ω) := by
  intro p hp
  change preservesFiberAt Ψ p
  rw [zeroNormalFiberTransitionOn_source] at hp
  have h : p ∈ interior {q | preservesFiberAt Ψ q} := hp.1.2
  have h' : p ∈ {q | preservesFiberAt Ψ q} := interior_subset h
  exact h'

theorem preservesZeroNormalFibers_zeroNormalFiberTransitionOn_symm
    (Ψ : OpenPartialHomeomorph Coord Coord) (Ω : Opens Coord) :
    PreservesZeroNormalFibers (zeroNormalFiberTransitionOn Ψ Ω).symm := by
  intro p hp
  change preservesFiberAt Ψ.symm p
  have h : p ∈ interior {q | preservesFiberAt Ψ.symm q} :=
    (mem_zeroNormalFiberTransitionOn_target_forward hp).2
  have h' : p ∈ {q | preservesFiberAt Ψ.symm q} := interior_subset h
  exact h'

/-- A fixed point on the slice with local preservation in both directions
belongs to the target of the restricted transition. -/
theorem mem_zeroNormalFiberTransitionOn_target_of_fixed
    {Ψ : OpenPartialHomeomorph Coord Coord} {Ω : Opens Coord} {p : O × Z}
    (hΩ : (p, 0) ∈ Ω) (hsrc : (p, 0) ∈ Ψ.source) (hfix : Ψ (p, 0) = (p, 0))
    (hf : ∀ᶠ q in 𝓝 p, preservesFiberAt Ψ q) (hi : ∀ᶠ q in 𝓝 p, preservesFiberAt Ψ.symm q) :
    (p, 0) ∈ (zeroNormalFiberTransitionOn Ψ Ω).target := by
  let Ψ' := zeroNormalFiberTransitionOn Ψ Ω
  have h : (p, 0) ∈ Ψ'.source := by
    rw [zeroNormalFiberTransitionOn_source]
    refine ⟨⟨hΩ, mem_interior_iff_mem_nhds.mpr hf⟩, hsrc, ?_⟩
    change Ψ (p, 0) ∈ Ω ⊓ zeroNormalFiberOpen Ψ.symm
    rw [hfix]
    exact ⟨hΩ, mem_interior_iff_mem_nhds.mpr hi⟩
  have ht := Ψ'.map_source h
  change Ψ (p, 0) ∈ Ψ'.target at ht
  rwa [hfix] at ht

section Weighted

variable [NormedSpace ℝ O] [NormedSpace ℝ Z] [NormedSpace ℝ N]
  [FiniteDimensional ℝ O] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ N]
  {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {e : OpenPartialHomeomorph ((O × Z) × N) X}
  (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
  (L : ((O × Z) × N) ≃L[ℝ] X) (D : 𝓓'((⊤ : Opens X), F))
  {Q : Opens O} {U : Opens Z} {V : Opens N}

local notation "Domain" => productTestDomain (productTestDomain Q U) V

omit [FiniteDimensional ℝ O] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ N] in
private theorem eval_jacobianNormalizedChartDistribution_eq_of_same_test [FiniteDimensional ℝ Coord]
    {R S : Opens Coord} (hR : R ≤ chartSource e) (hS : S ≤ chartSource e)
    (f : 𝓓(R, ℝ)) (g : 𝓓(S, ℝ)) (h : (f : Coord → ℝ) = g) :
    jacobianNormalizedChartDistribution he hei L hR D f = jacobianNormalizedChartDistribution he hei L hS D g := by
  let p := localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hR) f
  let q := localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hS) g
  let p' : 𝓓(chartSource e, ℝ) := TestFunction.monoCLM ℝ p
  let q' : 𝓓(chartSource e, ℝ) := TestFunction.monoCLM ℝ q
  change chartFullDistribution e hei D p' = chartFullDistribution e hei D q'
  have hp' : (p' : Coord → ℝ) = p := by simp [p', hR]
  have hq' : (q' : Coord → ℝ) = q := by simp [q', hS]
  congr 1
  ext x
  rw [congrFun hp', congrFun hq']
  simp only [p, q, localScalarMultiplierCLM_apply, h]

/-- Ambient signed covariance yields the local weighted pullback law for the
Jacobian-normalized distribution on any product inside the chart. -/
theorem hasLocalWeightedTestCovariance_zeroNormalFiberTransitionOn
    (hΩ : Domain ≤ chartSource e) (A : X ≃L[ℝ] X) (hA : |A.toContinuousLinearMap.det| = 1)
    (c : ℝ) (hD : ∀ g : 𝓓((⊤ : Opens X), ℝ), D (fullSmoothTestPullbackCLM A g) = c • D g) :
    HasLocalWeightedTestCovariance (jacobianNormalizedChartDistribution he hei L hΩ D)
      (zeroNormalFiberTransitionOn (chartLinearTransition e A) Domain)
      (chartAbsJacobian (ContinuousLinearEquiv.refl ℝ Coord) (chartLinearTransition e A)) c := by
  let Ψ := chartLinearTransition e A
  let R := zeroNormalFiberTransitionSource Ψ Domain
  let Ψ' := zeroNormalFiberTransitionOn Ψ Domain
  let S := chartTarget Ψ'
  have hR : R ≤ chartSource Ψ := zeroNormalFiberTransitionSource_le Ψ Domain
  have hRΩ : R ≤ Domain := zeroNormalFiberTransitionSource_le_domain Ψ Domain
  have hS : S ≤ chartTarget (chartLinearTransitionOn e A R) := le_rfl
  intro g hg
  let g' : 𝓓(S, ℝ) := ⟨g, g.contDiff, g.hasCompactSupport, hg⟩
  let p := weightedChartLinearTransitionPullbackCLM he hei A hR S g'
  let f : 𝓓(Domain, ℝ) := TestFunction.monoCLM ℝ p
  have hf : (f : Coord → ℝ) = p := by simp [f, hRΩ]
  have hSource : Ψ'.source = R := zeroNormalFiberTransitionOn_source Ψ Domain
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx
    rw [show (zeroNormalFiberTransitionOn (chartLinearTransition e A) Domain).source = (R : Set Coord) from hSource]
    exact p.tsupport_subset (hf ▸ hx)
  · intro x hx
    have hx' : x ∈ Ψ'.source := hx
    have hxR : x ∈ R := by rwa [hSource] at hx'
    have hp := weightedChartLinearTransitionPullbackCLM_apply_of_mem he hei A hR hS g' hxR
    change f x = chartAbsJacobian (ContinuousLinearEquiv.refl ℝ Coord) Ψ x * g (Ψ x)
    rw [congrFun hf, hp, mul_comm]
    rfl
  · rw [← eval_jacobianNormalizedChartDistribution_eq_of_same_test he hei L D (hRΩ.trans hΩ) hΩ p f hf.symm,
      ← eval_jacobianNormalizedChartDistribution_eq_of_same_test he hei L D
        (hS.trans (chartLinearTransitionOn_target_le A R)) hΩ g' g rfl]
    exact jacobianNormalizedChartDistribution_eval_weightedTransition he hei A hR hS L hA D c hD g'

variable [MeasurableSpace O] [BorelSpace O] (μ : Measure O) [μ.IsAddHaarMeasure]

local notation "Jet[" i "]" => (N [×i]→L[ℝ] ℝ)

/-- If the full and the orbit Jacobians at a fixed slice have absolute value one,
only the normal derivative acts on the leading covariant coefficient. -/
theorem orbitSliceCoefficient_eq_of_chartLinearTransition
    (hΩ : Domain ≤ chartSource e) (A : X ≃L[ℝ] X) (hA : |A.toContinuousLinearMap.det| = 1)
    (c : ℝ) (hD : ∀ g : 𝓓((⊤ : Opens X), ℝ), D (fullSmoothTestPullbackCLM A g) = c • D g)
    (χ : 𝓓(Q, ℝ)) (hχ : (∫ t, χ t ∂μ) = 1)
    (hFactor : ∀ f : 𝓓(Domain, ℝ), jacobianNormalizedChartDistribution he hei L hΩ D f =
      orbitSliceDistribution (jacobianNormalizedChartDistribution he hei L hΩ D) χ (orbitIntegratedTest μ f))
    (hQ : (0 : O) ∈ Q) (hV : (0 : N) ∈ V)
    (i : ℕ) (hord : HasTransverseJetOrder (orbitSliceDistribution
      (jacobianNormalizedChartDistribution he hei L hΩ D) χ) i)
    (ζ : 𝓓(V, ℝ)) (hζ : (ζ : N → ℝ) =ᶠ[𝓝 0] 1)
    (a : 𝓓(U, Jet[i])) (ha : ∀ z v (σ : Equiv.Perm (Fin i)), a z (v ∘ σ) = a z v)
    (M : N →L[ℝ] N)
    (hfix : ∀ z ∈ tsupport a, ((0, z), 0) ∈ (chartLinearTransition e A).source ∧
      chartLinearTransition e A ((0, z), 0) = ((0, z), 0))
    (hf : ∀ z ∈ tsupport a, ∀ᶠ p : O × Z in 𝓝 (0, z), preservesFiberAt (chartLinearTransition e A) p)
    (hi : ∀ z ∈ tsupport a, ∀ᶠ p : O × Z in 𝓝 (0, z), preservesFiberAt (chartLinearTransition e A).symm p)
    (horbit : ∀ z ∈ tsupport a, zeroNormalOrbitJacobian (chartLinearTransition e A) (0, z) = 1)
    (hnormal : ∀ z ∈ tsupport a, productNormalDerivative (chartLinearTransition e A) (0, z) = M) :
    let C := transverseProductJetCoefficient (orbitSliceDistribution
      (jacobianNormalizedChartDistribution he hei L hΩ D) χ) ζ i
    C (TestFunction.postcompCLM (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => M)) a) =
      c • C a := by
  let Ψ := chartLinearTransition e A
  let Ψ' := zeroNormalFiberTransitionOn Ψ Domain
  let w := chartAbsJacobian (ContinuousLinearEquiv.refl ℝ Coord) Ψ
  let T := jacobianNormalizedChartDistribution he hei L hΩ D
  let b := TestFunction.postcompCLM (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => M)) a
  have hΨ := contDiffOn_chartLinearTransition he hei A
  have hΨi := contDiffOn_chartLinearTransition_symm he hei A
  have hs : ContDiffOn ℝ ∞ Ψ' Ψ'.source := hΨ.mono fun _ hx => hx.1
  have hsi : ContDiffOn ℝ ∞ Ψ'.symm Ψ'.target := hΨi.mono fun _ hx => hx.1
  have hw : ContDiffOn ℝ ∞ w Ψ'.source :=
    (contDiffOn_chartAbsJacobian hΨ hΨi (ContinuousLinearEquiv.refl ℝ Coord)).mono fun _ hx => hx.1
  have ht (z : Z) (hz : z ∈ tsupport a) : ((0, z), 0) ∈ Ψ'.target :=
    mem_zeroNormalFiberTransitionOn_target_of_fixed ⟨⟨hQ, a.tsupport_subset hz⟩, hV⟩
      (hfix z hz).1 (hfix z hz).2 (hf z hz) (hi z hz)
  apply orbitSliceCoefficient_eq_of_localWeightedTestCovariance μ T χ hχ hFactor hQ hV
    hs hsi (preservesZeroNormalFibers_zeroNormalFiberTransitionOn Ψ Domain)
    (preservesZeroNormalFibers_zeroNormalFiberTransitionOn_symm Ψ Domain) hw c
    (hasLocalWeightedTestCovariance_zeroNormalFiberTransitionOn he hei L D hΩ A hA c hD) i hord ζ hζ a b ha ht
  intro z
  change (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => M)) (a z) =
    orbitJetTransportKernel Ψ' w i (z, 0) (a z)
  by_cases hz : z ∈ tsupport a
  · let p : Coord := ((0, z), 0)
    have hsrc : p ∈ Ψ.source := (hfix z hz).1
    have hp : Ψ p = p := (hfix z hz).2
    have hinv : Ψ.symm p = p :=
      (congrArg (fun x : Coord => Ψ.symm x) hp.symm).trans (Ψ.left_inv hsrc)
    have hj := chartAbsJacobian_mul_chartLinearTransition he hei A L hA hsrc
    change chartAbsJacobian L e (Ψ p) * w p = chartAbsJacobian L e p at hj
    rw [hp] at hj
    have hJ : chartAbsJacobian L e p ≠ 0 :=
      (chartAbsJacobian_pos he hei L (chartLinearTransition_source_le A hsrc)).ne'
    have hwn : w p = 1 := mul_left_cancel₀ hJ (hj.trans (mul_one _).symm)
    ext v
    rw [orbitJetTransportKernel_apply]
    change (a z) (fun k => M (v k)) =
      (w ((Ψ.symm p).1, 0) / zeroNormalOrbitJacobian Ψ (Ψ.symm p).1) •
        (a z) (fun k => productNormalDerivative Ψ (Ψ.symm p).1 (v k))
    rw [hinv]
    change _ = (w p / zeroNormalOrbitJacobian Ψ (0, z)) • _
    rw [hwn, horbit z hz, hnormal z hz, div_one, one_smul]
  · simp only [image_eq_zero_of_notMem_tsupport hz, map_zero]

end Weighted

end Langlands.HarmonicAnalysis
