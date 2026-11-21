import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Compact

/-! # Distributions commute with integrals of smooth test families

Let `μ` be a measure finite on compact sets, and let `Ω` be an open subset of a
finite-dimensional real normed space. Suppose the test functions `Φ m` are all
supported in a common compact `K ⊆ Ω`, vanish for `m` outside a compact set of
parameters, and have all spatial derivatives jointly continuous in `(m, x)`.
Then `x ↦ ∫ m, Φ m x ∂μ` is again a test function on `Ω`, its derivatives are the
integrals of the derivatives, and every distribution on `Ω` commutes with the integral.
-/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology BoundedContinuousFunction

namespace Langlands.Analysis

universe uX uA uE

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

section Derivative

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

omit [SecondCountableTopology X] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedSpace ℝ E] in
/-- A jointly continuous family vanishing off a compact parameter set is integrable
at every point. -/
theorem integrable_family_of_compact {Ψ : X → A → E}
    (hc : Continuous (fun q : X × A => Ψ q.1 q.2)) {S : Set X} (hS : IsCompact S)
    (hS0 : ∀ m ∉ S, ∀ x, Ψ m x = 0) (x : A) :
    Integrable (fun m => Ψ m x) μ :=
  (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hS fun m hm => hS0 m hm x)

/-- Differentiation under the integral sign for a family vanishing off a compact
parameter set, with jointly continuous values and derivatives. -/
theorem hasFDerivAt_integral_family {Ψ : X → A → E} {Ψ' : X → A → (A →L[ℝ] E)}
    (hd : ∀ m x, HasFDerivAt (Ψ m) (Ψ' m x) x)
    (hc : Continuous (fun q : X × A => Ψ q.1 q.2))
    (hc' : Continuous (fun q : X × A => Ψ' q.1 q.2))
    {S : Set X} (hS : IsCompact S) (hS0 : ∀ m ∉ S, ∀ x, Ψ m x = 0)
    (hS0' : ∀ m ∉ S, ∀ x, Ψ' m x = 0) (x₀ : A) :
    HasFDerivAt (fun x => ∫ m, Ψ m x ∂μ) (∫ m, Ψ' m x₀ ∂μ) x₀ := by
  have hB : IsCompact (S ×ˢ Metric.closedBall x₀ 1) := hS.prod (isCompact_closedBall x₀ 1)
  obtain ⟨C, hC⟩ := hB.exists_bound_of_continuousOn hc'.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x m => Ψ m x)
    (F' := fun x m => Ψ' m x) (bound := S.indicator fun _ => C)
    (Metric.ball_mem_nhds x₀ one_pos) (Eventually.of_forall fun x =>
      (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (integrable_family_of_compact μ hc hS hS0 x₀)
    (hc'.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable ?_ ?_ ?_
  · refine Eventually.of_forall fun m x hx => ?_
    by_cases hm : m ∈ S
    · rw [indicator_of_mem hm]
      exact hC (m, x) ⟨hm, Metric.ball_subset_closedBall hx⟩
    · rw [indicator_of_notMem hm, hS0' m hm x, norm_zero]
  · exact (integrable_indicator_iff hS.isClosed.measurableSet).mpr
      (integrableOn_const hS.measure_lt_top.ne)
  · exact Eventually.of_forall fun m x _ => hd m x

end Derivative

section Iterated

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hypotheses on a smooth family: each member is smooth, all iterated derivatives are
jointly continuous, and the family vanishes off a compact parameter set. -/
structure SmoothCompactFamily (Φ : X → A → E) : Prop where
  contDiff : ∀ m, ContDiff ℝ ∞ (Φ m)
  continuous_iteratedFDeriv :
    ∀ i : ℕ, Continuous (fun q : X × A => iteratedFDeriv ℝ i (Φ q.1) q.2)
  exists_compact : ∃ S : Set X, IsCompact S ∧ ∀ m ∉ S, ∀ x, Φ m x = 0

variable {μ}

omit [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [FiniteDimensional ℝ A] in
theorem SmoothCompactFamily.continuous {Φ : X → A → E} (h : SmoothCompactFamily Φ) :
    Continuous (fun q : X × A => Φ q.1 q.2) := by
  have hc := h.continuous_iteratedFDeriv 0
  have he : (fun q : X × A => Φ q.1 q.2) =
      (fun L => L 0) ∘ (fun q : X × A => iteratedFDeriv ℝ 0 (Φ q.1) q.2) := by
    funext q
    simp
  rw [he]
  exact (continuous_eval_const (0 : Fin 0 → A)).comp hc

/-- Iterated derivatives of the integral of a smooth compact family are the integrals
of the iterated derivatives. -/
theorem iteratedFDeriv_integral_family {Φ : X → A → E} (h : SmoothCompactFamily Φ) (i : ℕ) :
    iteratedFDeriv ℝ i (fun x => ∫ m, Φ m x ∂μ) =
      fun x => ∫ m, iteratedFDeriv ℝ i (Φ m) x ∂μ := by
  obtain ⟨S, hS, hS0⟩ := h.exists_compact
  have hzero (j : ℕ) (m : X) (hm : m ∉ S) (x : A) : iteratedFDeriv ℝ j (Φ m) x = 0 := by
    have : Φ m = 0 := funext fun y => hS0 m hm y
    rw [this]
    simp
  induction i with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ A E).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := μ) (fun m => Φ m x)).symm
  | succ i ih =>
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => A) E
    have hd : HasFDerivAt (fun x => ∫ m, iteratedFDeriv ℝ i (Φ m) x ∂μ)
        (∫ m, fderiv ℝ (iteratedFDeriv ℝ i (Φ m)) x ∂μ) x := by
      refine hasFDerivAt_integral_family μ
        (Ψ' := fun m y => fderiv ℝ (iteratedFDeriv ℝ i (Φ m)) y)
        (fun m y => ?_) (h.continuous_iteratedFDeriv i) ?_ hS
        (hzero i) (fun m hm y => ?_) x
      · exact ((h.contDiff m).differentiable_iteratedFDeriv
          (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt.hasFDerivAt
      · have he : (fun q : X × A => fderiv ℝ (iteratedFDeriv ℝ i (Φ q.1)) q.2) =
            e ∘ (fun q : X × A => iteratedFDeriv ℝ (i + 1) (Φ q.1) q.2) := by
          funext q
          simp [e, fderiv_iteratedFDeriv]
        rw [he]
        exact e.continuous.comp (h.continuous_iteratedFDeriv (i + 1))
      · rw [fderiv_iteratedFDeriv]
        simp [hzero (i + 1) m hm y]
        exact LinearIsometryEquiv.map_zero _
    rw [Function.comp_apply, hd.fderiv]
    change e.symm (∫ m, fderiv ℝ (iteratedFDeriv ℝ i (Φ m)) x ∂μ) = _
    have hcomm : ∫ m, e.symm (fderiv ℝ (iteratedFDeriv ℝ i (Φ m)) x) ∂μ =
        e.symm (∫ m, fderiv ℝ (iteratedFDeriv ℝ i (Φ m)) x ∂μ) :=
      ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (E := A →L[ℝ] A [×i]→L[ℝ] E)
        (F := ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => A) E)
        e.symm.toContinuousLinearEquiv _
    rw [← hcomm]
    congr 1

/-- The integral of a smooth compact family is smooth. -/
theorem contDiff_integral_family {Φ : X → A → E} (h : SmoothCompactFamily Φ) :
    ContDiff ℝ ∞ (fun x => ∫ m, Φ m x ∂μ) := by
  obtain ⟨S, hS, hS0⟩ := h.exists_compact
  apply contDiff_of_differentiable_iteratedFDeriv
  intro i _
  rw [iteratedFDeriv_integral_family h i]
  intro x
  have hzero (j : ℕ) (m : X) (hm : m ∉ S) (y : A) : iteratedFDeriv ℝ j (Φ m) y = 0 := by
    have : Φ m = 0 := funext fun z => hS0 m hm z
    rw [this]
    simp
  let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => A) E
  refine (hasFDerivAt_integral_family μ
    (Ψ' := fun m y => fderiv ℝ (iteratedFDeriv ℝ i (Φ m)) y)
    (fun m y => ?_) (h.continuous_iteratedFDeriv i) ?_ hS
    (hzero i) (fun m hm y => ?_) x).differentiableAt
  · exact ((h.contDiff m).differentiable_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt.hasFDerivAt
  · have he : (fun q : X × A => fderiv ℝ (iteratedFDeriv ℝ i (Φ q.1)) q.2) =
        e ∘ (fun q : X × A => iteratedFDeriv ℝ (i + 1) (Φ q.1) q.2) := by
      funext q
      simp [e, fderiv_iteratedFDeriv]
    rw [he]
    exact e.continuous.comp (h.continuous_iteratedFDeriv (i + 1))
  · rw [fderiv_iteratedFDeriv]
    simp [hzero (i + 1) m hm y]
    exact LinearIsometryEquiv.map_zero _

end Iterated

/-- The Banach space of jets of order at most `k`: the first `k + 1` derivatives of a
function on `A`, each as a bounded continuous function. -/
def JetSpace (A : Type uA) [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ) : Type uA :=
  Π i : Fin (k + 1), A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)

namespace JetSpace

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A] {k : ℕ}

set_option synthInstance.maxHeartbeats 400000

instance : NormedAddCommGroup (JetSpace A k) :=
  inferInstanceAs (NormedAddCommGroup (Π i : Fin (k + 1), A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)))

instance : NormedSpace ℂ (JetSpace A k) :=
  inferInstanceAs (NormedSpace ℂ (Π i : Fin (k + 1), A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)))

instance : NormedSpace ℝ (JetSpace A k) :=
  inferInstanceAs (NormedSpace ℝ (Π i : Fin (k + 1), A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)))

instance : CompleteSpace (JetSpace A k) :=
  inferInstanceAs (CompleteSpace (Π i : Fin (k + 1), A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)))

/-- The `i`-th component of a jet. -/
def proj (i : Fin (k + 1)) : JetSpace A k →L[ℝ] A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin (k + 1) => A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)) i

theorem norm_proj_le (y : JetSpace A k) (i : Fin (k + 1)) : ‖proj i y‖ ≤ ‖y‖ :=
  norm_le_pi_norm (G := fun i : Fin (k + 1) => A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ)) y i

theorem ext {y z : JetSpace A k} (h : ∀ i, proj i y = proj i z) : y = z :=
  funext h

/-- The jet of order `k` of a test function supported in `K`. -/
def jetCLM (K : Compacts A) (k : ℕ) : 𝓓_{K}(A, ℂ) →L[ℂ] JetSpace A k :=
  ContinuousLinearMap.pi (φ := fun i : Fin (k + 1) => A →ᵇ (A [×(i : ℕ)]→L[ℝ] ℂ))
    fun i => ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ (i : ℕ)

theorem proj_jetCLM (K : Compacts A) (i : Fin (k + 1)) (g : 𝓓_{K}(A, ℂ)) :
    proj i (jetCLM K k g) = ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ (i : ℕ) g :=
  rfl

end JetSpace

section Fubini

open ContDiffMapSupportedIn

variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

omit [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [FiniteDimensional ℝ A] in
/-- The `i`-th derivative, as a bounded continuous function, of a smooth compact family
with a common compact support depends continuously on the parameter. -/
theorem continuous_structureMapCLM_family {Φ : X → A → ℂ} (hΦ : SmoothCompactFamily Φ)
    {K : Compacts A} (f : X → 𝓓_{K}(A, ℂ)) (hf : ∀ m x, f m x = Φ m x) (i : ℕ) :
    Continuous (fun m => structureMapCLM ℂ ⊤ i (f m)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  let M := ContinuousMultilinearMap ℝ (fun _ : Fin i => A) ℂ
  let D (q : X) : C(K, M) :=
    ⟨fun x => iteratedFDeriv ℝ i (Φ q) x.val,
      (hΦ.continuous_iteratedFDeriv i).comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hD : Continuous D := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hΦ.continuous_iteratedFDeriv i).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfΦ (q : X) : (f q : A → ℂ) = Φ q := funext (hf q)
  have hle (q p : X) : dist (structureMapCLM ℂ ⊤ i (f q)) (structureMapCLM ℂ ⊤ i (f p)) ≤
      dist (D q) (D p) := by
    refine (BoundedContinuousFunction.dist_le dist_nonneg).2 fun x => ?_
    rw [structureMapCLM_top_apply, structureMapCLM_top_apply]
    by_cases hx : x ∈ K
    · rw [hfΦ q, hfΦ p]
      exact ContinuousMap.dist_apply_le_dist (f := D q) (g := D p) ⟨x, hx⟩
    · rw [(f q).iteratedFDeriv_zero_on_compl hx, (f p).iteratedFDeriv_zero_on_compl hx,
        dist_self]
      exact dist_nonneg
  refine continuous_iff_continuousAt.2 fun p => tendsto_iff_dist_tendsto_zero.2 ?_
  exact squeeze_zero (fun _ => dist_nonneg) (fun q => hle q p)
    (tendsto_iff_dist_tendsto_zero.1 (hD.tendsto p))

set_option synthInstance.maxHeartbeats 400000 in
/-- **Distributions commute with integrals of smooth compact families.** If `Φ m` is a
smooth compact family of functions supported in a fixed compact `K ⊆ Ω`, `φ m` are the
corresponding test functions and `ψ` the test function `x ↦ ∫ Φ m x dμ(m)`, then every
distribution `T` on `Ω` satisfies `T ψ = ∫ T (φ m) dμ(m)`. -/
theorem map_integral_family {Ω : Opens A} (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ)
    {Φ : X → A → ℂ} (hΦ : SmoothCompactFamily Φ) {K : Compacts A} (hK : (K : Set A) ⊆ Ω)
    (hΦK : ∀ m, ∀ x ∉ K, Φ m x = 0)
    (φ : X → 𝓓(Ω, ℂ)) (hφ : ∀ m x, φ m x = Φ m x)
    (ψ : 𝓓(Ω, ℂ)) (hψ : ∀ x, ψ x = ∫ m, Φ m x ∂μ) :
    T ψ = ∫ m, T (φ m) ∂μ := by
  have hsupp (m : X) : Function.support (Φ m) ⊆ (K : Set A) := fun x hx => by
    by_contra h
    exact hx (hΦK m x h)
  let φK : X → 𝓓_{K}(A, ℂ) := fun m =>
    ContDiffMapSupportedIn.of_support_subset (hΦ.contDiff m) (hsupp m)
  have hψsupp : Function.support (fun x => ∫ m, Φ m x ∂μ) ⊆ (K : Set A) := fun x hx => by
    by_contra h
    exact hx (by simp [hΦK _ x h])
  let ψK : 𝓓_{K}(A, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset (contDiff_integral_family hΦ) hψsupp
  let TK : 𝓓_{K}(A, ℂ) →L[ℂ] ℂ := T.comp (TestFunction.ofSupportedInCLM ℂ hK)
  have hφK (m : X) : φ m = TestFunction.ofSupportedIn hK (φK m) :=
    TestFunction.ext fun x => hφ m x
  have hψK : ψ = TestFunction.ofSupportedIn hK ψK :=
    TestFunction.ext fun x => hψ x
  -- a finite set of seminorms controls `TK`
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ A ℂ ⊤ K)
    ((normSeminorm ℂ ℂ).comp TK.toLinearMap) (continuous_norm.comp TK.continuous)
  let k : ℕ := s.sup id
  let J := JetSpace.jetCLM K k
  have hJinj : Function.Injective J := fun f g hfg =>
    structureMapCLM_zero_injective ℂ (congrArg (JetSpace.proj ⟨0, k.succ_pos⟩) hfg)
  have hbound (g : 𝓓_{K}(A, ℂ)) : ‖TK g‖ ≤ C * ‖J g‖ := by
    have h1 := hC g
    have h2 : s.sup (ContDiffMapSupportedIn.seminorm ℂ A ℂ ⊤ K) g ≤ ‖J g‖ :=
      Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => by
        rw [ContDiffMapSupportedIn.seminorm_apply]
        have hik : i < k + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
        exact JetSpace.norm_proj_le (J g) ⟨i, hik⟩
    calc ‖TK g‖ ≤ C * s.sup (ContDiffMapSupportedIn.seminorm ℂ A ℂ ⊤ K) g := h1
      _ ≤ C * ‖J g‖ := mul_le_mul_of_nonneg_left h2 C.coe_nonneg
  -- Hahn–Banach extension of `TK` through `J`
  let e := LinearEquiv.ofInjective J.toLinearMap (by exact hJinj)
  let f₀ : LinearMap.range J.toLinearMap →ₗ[ℂ] ℂ :=
    (TK : 𝓓_{K}(A, ℂ) →ₗ[ℂ] ℂ) ∘ₗ e.symm.toLinearMap
  have hJe (y : LinearMap.range J.toLinearMap) : J (e.symm y) = y := by
    have := congrArg Subtype.val (e.apply_symm_apply y)
    rwa [LinearEquiv.ofInjective_apply] at this
  let f : StrongDual ℂ (LinearMap.range J.toLinearMap) :=
    f₀.mkContinuous C fun y => by
      change ‖TK (e.symm y)‖ ≤ C * ‖(y : JetSpace A k)‖
      rw [← hJe y]
      exact hbound _
  obtain ⟨S, hS, -⟩ := exists_extension_norm_eq _ f
  have hST (g : 𝓓_{K}(A, ℂ)) : S (J g) = TK g := by
    have h := hS ⟨J g, g, rfl⟩
    have he : e.symm ⟨J g, g, rfl⟩ = g := e.symm_apply_apply g
    rw [h]
    change TK (e.symm ⟨J g, g, rfl⟩) = TK g
    rw [he]
  -- the family of jets is integrable and integrates to the jet of `ψK`
  obtain ⟨S0, hS0c, hS0⟩ := hΦ.exists_compact
  have hJc : Continuous (fun m => J (φK m)) := by
    change Continuous (fun m i => JetSpace.proj i (J (φK m)))
    exact continuous_pi fun i => continuous_structureMapCLM_family hΦ φK (fun _ _ => rfl) i
  have hJsupp : HasCompactSupport (fun m => J (φK m)) := by
    refine HasCompactSupport.intro hS0c fun m hm => ?_
    have h0 : φK m = 0 := ContDiffMapSupportedIn.ext fun x => hS0 m hm x
    simp [h0]
  have hint : Integrable (fun m => J (φK m)) μ := hJc.integrable_of_hasCompactSupport hJsupp
  have hJψ : J ψK = ∫ m, J (φK m) ∂μ := by
    apply JetSpace.ext
    intro i
    ext x : 1
    let L : JetSpace A k →L[ℝ] (A [×(i : ℕ)]→L[ℝ] ℂ) :=
      (BoundedContinuousFunction.evalCLM ℝ x).comp (JetSpace.proj i)
    change L (J ψK) = L (∫ m, J (φK m) ∂μ)
    rw [← L.integral_comp_comm hint]
    change iteratedFDeriv ℝ i (fun x => ∫ m, Φ m x ∂μ) x =
      ∫ m, iteratedFDeriv ℝ i (Φ m) x ∂μ
    rw [iteratedFDeriv_integral_family hΦ]
  calc T ψ = TK ψK := by rw [hψK]; rfl
    _ = S (J ψK) := (hST ψK).symm
    _ = S (∫ m, J (φK m) ∂μ) := by rw [hJψ]
    _ = ∫ m, S (J (φK m)) ∂μ := (S.integral_comp_comm hint).symm
    _ = ∫ m, T (φ m) ∂μ := by
      congr 1
      funext m
      rw [hST, hφK]
      rfl

end Fubini

end Langlands.Analysis
