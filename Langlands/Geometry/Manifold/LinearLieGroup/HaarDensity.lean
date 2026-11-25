import Langlands.Analysis.SmoothLinearDeterminant
import Langlands.Geometry.Manifold.LinearLieGroup.ProductCoordinates
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The Haar measure of a linear Lie group in coordinates of the second kind

For `h : IsExpLieAlgebra G 𝔤`, a basis `b` of `𝔤` and a left Haar measure `μ` on `G`:

* `IsExpLieAlgebra.exists_haar_density_prodExp`: near `1`, `μ` has a smooth positive density in
  the coordinates of the second kind `P(z) = ∏ᵢ exp (zᵢ bᵢ)`: `∫ ψ dμ = ∫_{B(0, r)} ψ(P z) ρ(z) dz`
  for `ψ` supported in `P (B(0, r))`;
* `IsExpLieAlgebra.exists_smooth_density_prodExp`: consequently every smooth function `K` on `ℝᵈ`
  supported near `0` is the pull-back of a smooth compactly supported function `κ` on `G`:
  `∫ κ φ dμ = ∫ K(t) φ(P t) dt`.

The density is not computed: it is obtained by averaging a smooth compactly supported function
over `G` and comparing with Haar measure through left invariance. The proof uses two separable
statements: the smoothness of the Jacobian determinant of a smooth family of maps
(`contDiffOn_det_fderiv_snd`), and the averaging identity
`integral_mul_integral_eq_setIntegral_of_forall` (Fubini and left invariance). The remaining
construction (the transition map of coordinates `Λ`, the cut-off functions, the change of variables
and the positivity of the density) is in the proof of `exists_haar_density_prodExp`.
-/

namespace Langlands.LinearLieGroup

open scoped Manifold ContDiff Topology
open NormedSpace Set Filter MeasureTheory Metric

/-- `g • f` is smooth on the whole space when `f` is smooth on an open set containing the support of
the smooth function `g`. -/
private theorem contDiff_smul_of_tsupport {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {O : Set V} (hO : IsOpen O) {f : V → F}
    {g : V → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiff ℝ ∞ g) (hgO : tsupport g ⊆ O) :
    ContDiff ℝ ∞ (fun x => g x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hg.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h' => hx (hgO h')
    have : (fun x => g x • f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- Parameter integrals: for a finite measure `ν`, a continuous `u` and a smooth compactly supported
`Ξ`, `z ↦ ∫ Ξ (u x, z) dν(x)` is of class `Cⁿ` for every `n` (differentiation under the integral,
by induction on `n`). -/
private theorem contDiff_integral_comp_of_hasCompactSupport {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] (ν : Measure X)
    [IsFiniteMeasure ν] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : X → V}
    (hu : Continuous u) (n : ℕ) :
    ∀ {W F : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [CompleteSpace F] (Ξ : V × W → F), ContDiff ℝ ∞ Ξ → HasCompactSupport Ξ →
      ContDiff ℝ n (fun z => ∫ x, Ξ (u x, z) ∂ν) := by
  induction n with
  | zero =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    obtain ⟨C, hC⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_dominated (bound := fun _ => C) (fun z => ?_) (fun z => ?_)
      (integrable_const C) (Eventually.of_forall fun a => ?_)
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a => hC _
    · exact hΞ.continuous.comp (continuous_const.prodMk continuous_id)
  | succ n ih =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    set Ξ' : V × W → (W →L[ℝ] F) := fun q => (fderiv ℝ Ξ q).comp (ContinuousLinearMap.inr ℝ V W)
      with hΞ'def
    have hΞ'c : ContDiff ℝ ∞ Ξ' :=
      ContDiff.clm_comp (𝕜 := ℝ) (g := fun q => fderiv ℝ Ξ q)
        (f := fun _ => ContinuousLinearMap.inr ℝ V W)
        (hΞ.fderiv_right (m := ∞) (by simp)) contDiff_const
    have hΞ's : HasCompactSupport Ξ' :=
      (hc.fderiv (𝕜 := ℝ)).comp_left
          (g := fun L : V × W →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ V W))
        (ContinuousLinearMap.zero_comp _)
    obtain ⟨C, hC⟩ := hΞ'c.continuous.bounded_above_of_compact_support hΞ's
    obtain ⟨C₀, hC₀⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    have hdiff : ∀ (v : V) (z : W), HasFDerivAt (fun z => Ξ (v, z)) (Ξ' (v, z)) z := by
      intro v z
      have h1 : HasFDerivAt Ξ (fderiv ℝ Ξ (v, z)) (v, z) :=
        ((hΞ.differentiable (by simp)) (v, z)).hasFDerivAt
      exact h1.comp z ((hasFDerivAt_const v z).prodMk (hasFDerivAt_id z))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun z => ∫ x, Ξ' (u x, z) ∂ν, ih Ξ' hΞ'c hΞ's, fun z₀ => ?_⟩
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C)
      (F := fun z a => Ξ (u a, z)) (F' := fun z a => Ξ' (u a, z))
      univ_mem (Eventually.of_forall fun z => ?_) ?_ ?_ ?_ (integrable_const C) ?_
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Integrable.of_bound
        (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable C₀
        (Eventually.of_forall fun a => hC₀ _)
    · exact (hΞ'c.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a z _ => hC _
    · exact Eventually.of_forall fun a z _ => hdiff (u a) z

/-- The Jacobian determinant in the second variable, `q ↦ det (∂₂Λ (q))`, of a map smooth on an open
set is smooth there. -/
theorem contDiffOn_det_fderiv_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Λ : E × (Fin d → ℝ) → (Fin d → ℝ)} {O : Set (E × (Fin d → ℝ))} (hO : IsOpen O)
    (hΛ : ContDiffOn ℝ ∞ Λ O) :
    ContDiffOn ℝ ∞ (fun q : E × (Fin d → ℝ) => (fderiv ℝ (fun z' => Λ (q.1, z')) q.2).det) O := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hΛq : ContDiffAt ℝ ∞ Λ q := hΛ.contDiffAt (hO.mem_nhds hq)
  have hfd : ContDiffAt ℝ ∞
      (fun q' : E × (Fin d → ℝ) => fderiv ℝ (fun z' => Λ (q'.1, z')) q'.2) q := by
    refine ContDiffAt.fderiv (f := fun (q' : E × (Fin d → ℝ)) (z' : Fin d → ℝ) => Λ (q'.1, z'))
      (g := Prod.snd) (n := ∞) ?_ contDiffAt_snd (by simp)
    have hpr : ContDiffAt ℝ ∞
        (fun x : (E × (Fin d → ℝ)) × (Fin d → ℝ) => (x.1.1, x.2)) (q, q.2) :=
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
    exact hΛq.comp (q, q.2) hpr
  exact Langlands.Analysis.contDiff_continuousLinearMap_det.contDiffAt.comp q hfd

/-- **Averaging over left translates.** Let `μ` be a left Haar measure, `P : ℝᵈ → G` continuous, and
`β`, `Θ`, `ψ` continuous with compact support. If, for every `x`,
`∫ β(t) ψ(P t · x) dt = ∫_s ψ(P z) Θ(x, z) dz`, then
`(∫ β) ∫ ψ dμ = ∫_s ψ(P z) (∫ Θ(x, z) dμ(x)) dz`.
Integrate the hypothesis over `x`; on the left, Fubini and the left invariance of `μ` give
`(∫ β) ∫ ψ dμ`, on the right Fubini gives the stated integral. -/
theorem integral_mul_integral_eq_setIntegral_of_forall
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {d : ℕ} {P : (Fin d → ℝ) → G} (hP : Continuous P)
    {β : (Fin d → ℝ) → ℝ} (hβ : Continuous β) (hβs : HasCompactSupport β)
    {Θ : G → (Fin d → ℝ) → ℝ} (hΘ : Continuous (Function.uncurry Θ))
    (hΘs : HasCompactSupport (Function.uncurry Θ)) {s : Set (Fin d → ℝ)} (hs : MeasurableSet s)
    {ψ : G → ℂ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hC : ∀ x, ∫ t, (β t : ℂ) * ψ (P t * x) = ∫ z in s, ψ (P z) * (Θ x z : ℂ)) :
    ((∫ t, β t : ℝ) : ℂ) * ∫ y, ψ y ∂μ = ∫ z in s, ψ (P z) * ((∫ x, Θ x z ∂μ : ℝ) : ℂ) := by
  have hint1 : Integrable (Function.uncurry fun (t : Fin d → ℝ) (x : G) =>
      (β t : ℂ) * ψ (P t * x)) (volume.prod μ) := by
    have hcont : Continuous (Function.uncurry fun (t : Fin d → ℝ) (x : G) =>
        (β t : ℂ) * ψ (P t * x)) :=
      (Complex.continuous_ofReal.comp (hβ.comp continuous_fst)).mul
        (hψ.comp ((hP.comp continuous_fst).mul continuous_snd))
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
      ((hβs.isCompact.prod hψs.isCompact).image
        (continuous_fst.prodMk ((hP.comp continuous_fst).inv.mul continuous_snd))) ?_)
    intro q hq
    by_contra hne
    apply hq
    have hβq : β q.1 ≠ 0 := fun h0 => hne (by
      show (β q.1 : ℂ) * ψ (P q.1 * q.2) = 0
      rw [h0, Complex.ofReal_zero, zero_mul])
    have hψq : ψ (P q.1 * q.2) ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨(q.1, P q.1 * q.2), ⟨subset_tsupport _ hβq, subset_tsupport _ hψq⟩, ?_⟩
    show (q.1, (P q.1)⁻¹ * (P q.1 * q.2)) = q
    rw [inv_mul_cancel_left]
  have hint2 : Integrable (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
      ψ (P z) * (Θ x z : ℂ)) (μ.prod (volume.restrict s)) := by
    have hcont : Continuous (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
        ψ (P z) * (Θ x z : ℂ)) :=
      (hψ.comp (hP.comp continuous_snd)).mul (Complex.continuous_ofReal.comp hΘ)
    have hi : Integrable (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
        ψ (P z) * (Θ x z : ℂ)) (μ.prod volume) := by
      refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hΘs.isCompact ?_)
      intro q hq
      have h0 : Function.uncurry Θ q = 0 := image_eq_zero_of_notMem_tsupport hq
      show ψ (P q.2) * (Θ q.1 q.2 : ℂ) = 0
      rw [show Θ q.1 q.2 = Function.uncurry Θ q from rfl, h0, Complex.ofReal_zero, mul_zero]
    have e : μ.prod (volume.restrict s) = (μ.prod volume).restrict (univ ×ˢ s) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]; exact hi.restrict
  have hA : ((∫ t, β t : ℝ) : ℂ) * ∫ y, ψ y ∂μ = ∫ t, ∫ x, (β t : ℂ) * ψ (P t * x) ∂μ := by
    have e1 : ∀ t, ∫ x, (β t : ℂ) * ψ (P t * x) ∂μ = (β t : ℂ) * ∫ y, ψ y ∂μ := by
      intro t; rw [integral_const_mul, integral_mul_left_eq_self]
    simp_rw [e1]
    rw [integral_mul_const, integral_complex_ofReal]
  rw [hA, integral_integral_swap hint1]
  have e2 : (fun x : G => ∫ t, (β t : ℂ) * ψ (P t * x)) = fun x =>
      ∫ z in s, ψ (P z) * (Θ x z : ℂ) := funext hC
  rw [e2, integral_integral_swap hint2]
  refine setIntegral_congr_fun hs (fun z _ => ?_)
  show ∫ x, ψ (P z) * (Θ x z : ℂ) ∂μ = ψ (P z) * ((∫ x, Θ x z ∂μ : ℝ) : ℂ)
  rw [integral_const_mul, integral_complex_ofReal]

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

/-- **Haar measure in coordinates of the second kind.** There are `r > 0`, a smooth function `ρ`
positive on the ball `B(0, r)` of `ℝᵈ`, an open set `W ⊆ G` and a map `c : G → ℝᵈ` inverting
`P = prodExp b` (`P` maps the ball into `W`, `c ∘ P = id` on the ball, `P ∘ c = id` on `W`, and
`Y ↦ c (g exp Y)` is smooth at `0` for `g ∈ W`), such that
`∫ ψ dμ = ∫_{B(0, r)} ψ(P z) ρ(z) dz` for every continuous compactly supported `ψ` supported in
`P (B(0, r))`.

The density is `ρ(z) = D(z) / ∫ β`, where `D(z) = ∫ Ξ(x⁻¹, z) dμ(x)` for a smooth compactly
supported function `Ξ(a, z) = θ(z) χ(P(z) a) β(Λ(a, z)) J(a, z)`; here `Λ(a, z)` are the
coordinates of `P(z) a`, `J` is the Jacobian of `Λ` in `z`, and `θ`, `χ`, `β` are bump functions.
The change of variables `s = Λ(x⁻¹, z)` turns `∫ β(s) ψ(P s · x) ds` into
`∫_{B(0, r)} ψ(P z) Ξ(x⁻¹, z) dz`, and `integral_mul_integral_eq_setIntegral_of_forall` concludes.
`D` is smooth by differentiation under the integral, and positive on the ball because the integrand
is nonnegative and positive at `x = P z`. -/
theorem exists_haar_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (r : ℝ) (ρ : (Fin d → ℝ) → ℝ) (c : G → (Fin d → ℝ)) (W : Set G), 0 < r ∧
      ContDiff ℝ ∞ ρ ∧ (∀ z ∈ ball (0 : Fin d → ℝ) r, 0 < ρ z) ∧ IsOpen W ∧
      (∀ z ∈ ball (0 : Fin d → ℝ) r, h.prodExp (⇑b) z ∈ W ∧ c (h.prodExp (⇑b) z) = z) ∧
      (∀ y ∈ W, h.prodExp (⇑b) (c y) = y) ∧
      (∀ g ∈ W, ContDiffAt ℝ ∞ (fun Y : 𝔤 => c (g * h.expG Y)) 0) ∧
      ∀ ψ₀ : G → ℂ, Continuous ψ₀ → HasCompactSupport ψ₀ →
        tsupport ψ₀ ⊆ h.prodExp (⇑b) '' ball 0 r →
        ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (h.prodExp (⇑b) z) * (ρ z : ℂ) := by
  classical
  have : SecondCountableTopology G := secondCountableTopology_subgroup G
  have : LocallyCompactSpace G := h.locallyCompactSpace
  obtain ⟨S, T, Ψ, hSo, hTo, h0S, hST, hTS, hleft, hright, hΨ, hSN⟩ := h.exists_prodExp_coord b
  set p : (Fin d → ℝ) → 𝔸 := prodExpVal (fun i => (b i : 𝔸)) with hp_def
  set P : (Fin d → ℝ) → G := h.prodExp ⇑b with hP_def
  have hPv : ∀ t, (((P t : G) : 𝔸ˣ) : 𝔸) = p t := fun t => h.val_prodExp _ t
  have hpc : Continuous p := (contDiff_prodExpVal _).continuous
  have hPc : Continuous P := h.continuous_prodExp _
  have hp0 : p 0 = 1 := prodExpVal_zero _
  have hP0 : P 0 = 1 := Subtype.ext (Units.ext (by rw [hPv, hp0]; rfl))
  have hΨ0 : Ψ 0 = 0 := by
    have := hleft 0 h0S; rwa [prodExpCoord_zero] at this

  set c : G → (Fin d → ℝ) := fun y => Ψ (logCoord b (((y : 𝔸ˣ) : 𝔸))) with hc_def
  set Wc : Set G := {y | (((y : 𝔸ˣ) : 𝔸)) ∈ h.nhdOne ∧ logCoord b (((y : 𝔸ˣ) : 𝔸)) ∈ T}
    with hWc_def
  have hlogC : ContinuousOn (logCoord b) h.nhdOne :=
    (contDiffOn_logCoord b).continuousOn.mono h.nhdOne_subset_target
  have hNT : IsOpen (h.nhdOne ∩ logCoord b ⁻¹' T) :=
    hlogC.isOpen_inter_preimage h.isOpen_nhdOne hTo
  have hWco : IsOpen Wc := hNT.preimage (continuous_val_val G)
  have hN : ∀ w ∈ T, p (Ψ w) ∈ h.nhdOne := fun w hw => hSN _ (hTS hw)
  have hPcW : ∀ y ∈ Wc, P (c y) = y := fun y hy => h.prodExp_coord_eq b hright hN hy.1 hy.2
  have hcP : ∀ z ∈ S, c (P z) = z := by
    intro z hz
    show Ψ (logCoord b (((P z : G) : 𝔸ˣ) : 𝔸)) = z
    rw [hPv]; exact hleft z hz
  have hPW : ∀ z ∈ S, P z ∈ Wc := fun z hz =>
    ⟨by rw [hPv]; exact hSN z hz, by rw [hPv]; exact hST hz⟩

  set Λ : 𝔸 × (Fin d → ℝ) → (Fin d → ℝ) := fun q => Ψ (logCoord b (p q.2 * q.1)) with hΛ_def
  set O : Set (𝔸 × (Fin d → ℝ)) := {q | p q.2 * q.1 ∈ h.nhdOne ∧ logCoord b (p q.2 * q.1) ∈ T}
    with hO_def
  have hm : ContDiff ℝ ∞ (fun q : 𝔸 × (Fin d → ℝ) => p q.2 * q.1) :=
    ((contDiff_prodExpVal _).comp contDiff_snd).mul contDiff_fst
  have hOo : IsOpen O := hNT.preimage hm.continuous
  have hΛs : ContDiffOn ℝ ∞ Λ O := by
    have h1 : ContDiffOn ℝ ∞ (fun q : 𝔸 × (Fin d → ℝ) => logCoord b (p q.2 * q.1)) O :=
      (contDiffOn_logCoord b).comp hm.contDiffOn (fun q hq => h.nhdOne_subset_target hq.1)
    exact hΨ.comp h1 (fun q hq => hq.2)
  set J : 𝔸 × (Fin d → ℝ) → ℝ := fun q => (fderiv ℝ (fun z' => Λ (q.1, z')) q.2).det
    with hJ_def
  have hJs : ContDiffOn ℝ ∞ J O := contDiffOn_det_fderiv_snd hOo hΛs
  set Og : Set (𝔸 × (Fin d → ℝ)) := O ∩ J ⁻¹' Ioi 0 with hOg_def
  have hOgo : IsOpen Og := hJs.continuousOn.isOpen_inter_preimage hOo isOpen_Ioi
  obtain ⟨R, hR, hRS⟩ : ∃ R > 0, closedBall (0 : Fin d → ℝ) R ⊆ S := by
    obtain ⟨R', hR', hR'S⟩ := Metric.isOpen_iff.1 hSo 0 h0S
    exact ⟨R' / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hR'S⟩
  have hJ1 : ∀ z ∈ S, J (1, z) = 1 := by
    intro z hz
    have heq : (fun z' => Λ ((1 : 𝔸), z')) =ᶠ[𝓝 z] id := by
      filter_upwards [hSo.mem_nhds hz] with z' hz'
      show Ψ (logCoord b (p z' * 1)) = z'
      rw [mul_one]; exact hleft z' hz'
    show (fderiv ℝ (fun z' => Λ ((1 : 𝔸), z')) z).det = 1
    rw [heq.fderiv_eq, fderiv_id]
    show LinearMap.det (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = 1
    exact LinearMap.det_id
  have hsub : ({1} : Set 𝔸) ×ˢ closedBall (0 : Fin d → ℝ) R ⊆ Og := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    rw [mem_singleton_iff] at ha; subst ha
    have hzS := hRS hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show p z * 1 ∈ h.nhdOne
      rw [mul_one]; exact hSN z hzS
    · show logCoord b (p z * 1) ∈ T
      rw [mul_one]; exact hST hzS
    · show 0 < J (1, z)
      rw [hJ1 z hzS]; exact one_pos
  obtain ⟨u, v, hu, hv, h1u, hRv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall 0 R) hOgo hsub
  set Q : (Fin d → ℝ) × 𝔸 → 𝔸 := fun q => ((((P q.1)⁻¹ : G) : 𝔸ˣ) : 𝔸) * q.2 with hQ_def
  have hQc : Continuous Q :=
    ((continuous_val_val G).comp (hPc.comp continuous_fst).inv).mul continuous_snd
  have hQ0 : Q (0, 1) = 1 := by simp [hQ_def, hP0]
  have hQp : ∀ z a, Q (z, p z * a) = a := by
    intro z a
    show ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) * (p z * a) = a
    rw [← hPv, ← mul_assoc]
    have : ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) * (((P z : G) : 𝔸ˣ) : 𝔸) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, one_mul]
  obtain ⟨δ, hδ, hδu⟩ : ∃ δ > 0, ∀ z w, dist z 0 < δ → dist w 1 < δ → Q (z, w) ∈ u := by
    have hmem : Q ⁻¹' u ∈ 𝓝 ((0 : Fin d → ℝ), (1 : 𝔸)) :=
      hQc.continuousAt.preimage_mem_nhds (hu.mem_nhds (by rw [hQ0]; exact h1u rfl))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨δ, hδ, fun z w hz hw => hball ?_⟩
    rw [mem_ball, Prod.dist_eq]; exact max_lt hz hw
  obtain ⟨δ₂, hδ₂, hδ₂p⟩ : ∃ δ₂ > 0, ∀ z, dist z 0 < δ₂ → dist (p z) 1 < δ / 4 := by
    obtain ⟨δ₂, hδ₂, H⟩ := Metric.continuousAt_iff.1 hpc.continuousAt (δ / 4) (by positivity)
    exact ⟨δ₂, hδ₂, fun z hz => by rw [← hp0]; exact H hz⟩

  set r : ℝ := min (δ / 4) (R / 2) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  set rβ : ℝ := min (δ₂ / 2) (R / 2) with hrβ_def
  have hrβ : 0 < rβ := lt_min (by positivity) (by positivity)
  have h2rR : 2 * r ≤ R := by have := min_le_right (δ / 4) (R / 2); linarith
  have h2rδ : 2 * r < δ := by have := min_le_left (δ / 4) (R / 2); linarith
  have hrβR : rβ ≤ R := by have := min_le_right (δ₂ / 2) (R / 2); linarith
  have hrβδ : rβ < δ₂ := by have := min_le_left (δ₂ / 2) (R / 2); linarith
  let θ : ContDiffBump (0 : Fin d → ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  let β : ContDiffBump (0 : Fin d → ℝ) := ⟨rβ / 2, rβ, by positivity, by linarith⟩
  let χ : ContDiffBump (1 : 𝔸) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hχ1 : ∀ w, dist w 1 < δ / 4 → χ w = 1 := fun w hw =>
    χ.one_of_mem_closedBall (mem_closedBall.2 hw.le)
  have hχ0 : ∀ w, χ w ≠ 0 → dist w 1 < δ / 2 := fun w hw => by
    have : w ∈ Function.support χ := hw
    rw [χ.support_eq] at this; exact this
  have hθ1 : ∀ z ∈ ball (0 : Fin d → ℝ) r, θ z = 1 := fun z hz =>
    θ.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hθ0 : ∀ z, θ z ≠ 0 → dist z 0 < 2 * r := fun z hz => by
    have : z ∈ Function.support θ := hz
    rw [θ.support_eq] at this; exact this
  have hβ0 : ∀ s, β s ≠ 0 → dist s 0 < rβ := fun s hs => by
    have : s ∈ Function.support β := hs
    rw [β.support_eq] at this; exact this
  have hps : ∀ s, dist s 0 < rβ → dist (p s) 1 < δ / 4 := fun s hs => hδ₂p s (hs.trans hrβδ)
  have hUV : ∀ a z, dist z 0 ≤ 2 * r → dist (p z * a) 1 < δ → (a, z) ∈ Og := by
    intro a z hz hw
    have h1 : Q (z, p z * a) ∈ u := hδu z _ (by linarith) hw
    rw [hQp] at h1
    exact huv ⟨h1, hRv (mem_closedBall.2 (by linarith))⟩

  have hkey : ∀ (x : G) (z : Fin d → ℝ), ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∈ O →
      P (Λ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z)) = P z * x⁻¹ := by
    intro x z hq
    have hv : (((P z * x⁻¹ : G) : 𝔸ˣ) : 𝔸) = p z * (((x⁻¹ : G) : 𝔸ˣ) : 𝔸) := by
      rw [Subgroup.coe_mul, Units.val_mul, hPv]
    have hW : P z * x⁻¹ ∈ Wc := ⟨by rw [hv]; exact hq.1, by rw [hv]; exact hq.2⟩
    have := hPcW _ hW
    rwa [show c (P z * x⁻¹) = Λ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) by
      show Ψ (logCoord b (((P z * x⁻¹ : G) : 𝔸ˣ) : 𝔸)) = _; rw [hv]] at this

  set g₀ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => θ q.2 * χ (p q.2 * q.1) with hg₀_def
  set f₀ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => β (Λ q) * J q with hf₀_def
  set Ξ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => g₀ q • f₀ q with hΞ_def
  have hg₀c : ContDiff ℝ ∞ g₀ := (θ.contDiff.comp contDiff_snd).mul (χ.contDiff.comp hm)
  have hf₀ : ContDiffOn ℝ ∞ f₀ Og :=
    ((β.contDiff.comp_contDiffOn hΛs).mul hJs).mono inter_subset_left
  set K₀ : Set (𝔸 × (Fin d → ℝ)) := {q | dist q.2 0 ≤ 2 * r ∧ dist (p q.2 * q.1) 1 ≤ δ / 2}
    with hK₀_def
  have hK₀cl : IsClosed K₀ :=
    (isClosed_le (continuous_snd.dist continuous_const) continuous_const).inter
      (isClosed_le (hm.continuous.dist continuous_const) continuous_const)
  have hg₀K : ∀ q, g₀ q ≠ 0 → q ∈ K₀ := by
    intro q hq
    have h1 : θ q.2 ≠ 0 := left_ne_zero_of_mul hq
    have h2 : χ (p q.2 * q.1) ≠ 0 := right_ne_zero_of_mul hq
    exact ⟨(hθ0 _ h1).le, (hχ0 _ h2).le⟩
  have hK₀Og : K₀ ⊆ Og := fun q hq => hUV q.1 q.2 hq.1 (by linarith [hq.2])
  have htsg : tsupport g₀ ⊆ K₀ := closure_minimal (fun q hq => hg₀K q hq) hK₀cl
  have hΞc : ContDiff ℝ ∞ Ξ := contDiff_smul_of_tsupport hOgo hf₀ hg₀c (htsg.trans hK₀Og)
  have hK₀cpt : IsCompact K₀ := by
    have hsub' : K₀ ⊆ (fun q : (Fin d → ℝ) × 𝔸 => (Q q, q.1)) ''
        (closedBall 0 (2 * r) ×ˢ closedBall 1 (δ / 2)) := by
      intro q hq
      refine ⟨(q.2, p q.2 * q.1), ⟨mem_closedBall.2 hq.1, mem_closedBall.2 hq.2⟩, ?_⟩
      show (Q (q.2, p q.2 * q.1), q.2) = q
      rw [hQp]
    exact (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
      (hQc.prodMk continuous_fst)).of_isClosed_subset hK₀cl hsub'
  have hΞ0 : ∀ q, q ∉ K₀ → Ξ q = 0 := by
    intro q hq
    have : g₀ q = 0 := by by_contra hne; exact hq (hg₀K q hne)
    simp [hΞ_def, this]
  have hΞs : HasCompactSupport Ξ := HasCompactSupport.intro hK₀cpt hΞ0
  have hΞnn : ∀ q, 0 ≤ Ξ q := by
    intro q
    by_cases hq : q ∈ K₀
    · have hJq : 0 < J q := (hK₀Og hq).2
      exact smul_nonneg (mul_nonneg θ.nonneg χ.nonneg) (mul_nonneg β.nonneg hJq.le)
    · rw [hΞ0 q hq]

  set X₀ : Set G := (fun q : (Fin d → ℝ) × (Fin d → ℝ) => (P q.1)⁻¹ * P q.2) ''
    (closedBall 0 rβ ×ˢ closedBall 0 (2 * r)) with hX₀_def
  have hX₀ : IsCompact X₀ :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
      ((hPc.comp continuous_fst).inv.mul (hPc.comp continuous_snd))
  have hsuppx : ∀ (x : G) (z : Fin d → ℝ), Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ≠ 0 →
      x ∈ X₀ ∧ dist z 0 < 2 * r := by
    intro x z hne
    set a : 𝔸 := (((x⁻¹ : G) : 𝔸ˣ) : 𝔸)
    have hg : g₀ (a, z) ≠ 0 := left_ne_zero_of_mul hne
    have hf : f₀ (a, z) ≠ 0 := right_ne_zero_of_mul hne
    have hzr : dist z 0 < 2 * r := hθ0 z (left_ne_zero_of_mul hg)
    have hw : dist (p z * a) 1 < δ / 2 := hχ0 _ (right_ne_zero_of_mul hg)
    have hq : (a, z) ∈ Og := hUV a z hzr.le (by linarith)
    have hs : dist (Λ (a, z)) 0 < rβ := hβ0 _ (left_ne_zero_of_mul hf)
    have hk := hkey x z hq.1
    refine ⟨⟨(Λ (a, z), z), ⟨mem_closedBall.2 hs.le, mem_closedBall.2 hzr.le⟩, ?_⟩, hzr⟩
    show (P (Λ (a, z)))⁻¹ * P z = x
    rw [hk]; group
  set D : (Fin d → ℝ) → ℝ := fun z => ∫ x, Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∂μ with hD_def
  have hu_c : Continuous (fun x : G => (((x⁻¹ : G) : 𝔸ˣ) : 𝔸)) :=
    (continuous_val_val G).comp continuous_inv
  have hDeq : D = fun z => ∫ x, Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∂(μ.restrict X₀) := by
    funext z
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    by_contra hne; exact hx (hsuppx x z hne).1
  have : IsFiniteMeasure (μ.restrict X₀) := isFiniteMeasure_restrict.2 hX₀.measure_lt_top.ne
  have hDs : ContDiff ℝ ∞ D := by
    rw [hDeq, contDiff_infty]
    intro n
    exact contDiff_integral_comp_of_hasCompactSupport (μ.restrict X₀) hu_c n Ξ hΞc hΞs
  have hDpos : ∀ z ∈ ball (0 : Fin d → ℝ) r, 0 < D z := by
    intro z hz
    set F : G → ℝ := fun x => Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) with hF_def
    have hFc : Continuous F := hΞc.continuous.comp (hu_c.prodMk continuous_const)
    have hFs : HasCompactSupport F := HasCompactSupport.intro hX₀ (fun x hx => by
      by_contra hne; exact hx (hsuppx x z hne).1)
    have hFi : Integrable F μ := hFc.integrable_of_hasCompactSupport hFs
    have hFpos : 0 < F (P z) := by
      set a₀ : 𝔸 := ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) with ha₀
      have h1 : p z * a₀ = 1 := by
        rw [ha₀, ← hPv, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      have hzr : dist z 0 < r := mem_ball.1 hz
      have hq : (a₀, z) ∈ Og := hUV _ z (by linarith) (by rw [h1, dist_self]; exact hδ)
      have hΛ0 : Λ (a₀, z) = 0 := by
        show Ψ (logCoord b (p z * a₀)) = 0
        rw [h1, logCoord_one, hΨ0]
      have hg1 : g₀ (a₀, z) = 1 := by
        show θ z * χ (p z * a₀) = 1
        rw [h1, hθ1 z hz, χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le), one_mul]
      show 0 < g₀ (a₀, z) • f₀ (a₀, z)
      rw [hg1, one_smul]
      show 0 < β (Λ (a₀, z)) * J (a₀, z)
      rw [hΛ0, β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le), one_mul]
      exact hq.2
    show 0 < ∫ x, F x ∂μ
    rw [integral_pos_iff_support_of_nonneg (fun x => hΞnn _) hFi]
    exact hFc.isOpen_support.measure_pos μ ⟨P z, hFpos.ne'⟩

  have hC : ∀ (ψ₀ : G → ℂ), tsupport ψ₀ ⊆ P '' ball 0 r → ∀ x : G,
      ∫ s, (β s : ℂ) * ψ₀ (P s * x) =
        ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ) := by
    intro ψ₀ hψsupp x
    set a : 𝔸 := (((x⁻¹ : G) : 𝔸ˣ) : 𝔸) with ha
    set U : Set (Fin d → ℝ) := ball 0 r ∩ {z | dist (p z * a) 1 < δ / 2} with hU_def
    have hUo : IsOpen U := isOpen_ball.inter
      (isOpen_lt ((hpc.mul continuous_const).dist continuous_const) continuous_const)
    have hUOg : ∀ z ∈ U, (a, z) ∈ Og := fun z hz =>
      hUV a z (by have := mem_ball.1 hz.1; linarith)
        (by have h2 : dist (p z * a) 1 < δ / 2 := hz.2; linarith)
    set Λx : (Fin d → ℝ) → (Fin d → ℝ) := fun z => Λ (a, z) with hΛx_def
    have hΛxd : ∀ z ∈ U, HasFDerivWithinAt Λx (fderiv ℝ Λx z) U z := by
      intro z hz
      have h1 : ContDiffAt ℝ ∞ Λ (a, z) := hΛs.contDiffAt (hOo.mem_nhds (hUOg z hz).1)
      have h2 : DifferentiableAt ℝ Λx z :=
        (h1.differentiableAt (by simp)).comp z
          ((differentiableAt_const a).prodMk differentiableAt_id)
      exact h2.hasFDerivAt.hasFDerivWithinAt
    have hΛxP : ∀ z ∈ U, P (Λx z) = P z * x⁻¹ := fun z hz => hkey x z (hUOg z hz).1
    have hballS : ∀ z ∈ ball (0 : Fin d → ℝ) r, z ∈ S := fun z hz =>
      hRS (mem_closedBall.2 (by have := mem_ball.1 hz; linarith))
    have hinj : InjOn Λx U := by
      intro z₁ hz₁ z₂ hz₂ heq
      have e1 := hΛxP z₁ hz₁
      have e2 := hΛxP z₂ hz₂
      rw [heq, e2] at e1
      have e3 : P z₁ = P z₂ := (mul_right_cancel e1).symm
      rw [← hcP z₁ (hballS z₁ hz₁.1), ← hcP z₂ (hballS z₂ hz₂.1), e3]
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hUo.measurableSet hΛxd
      hinj (fun s => (β s : ℂ) * ψ₀ (P s * x))
    have hL : ∫ s in Λx '' U, (β s : ℂ) * ψ₀ (P s * x) = ∫ s, (β s : ℂ) * ψ₀ (P s * x) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
      by_contra hne
      have hβs : β s ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      have hψs : ψ₀ (P s * x) ≠ 0 := right_ne_zero_of_mul hne
      have hsr : dist s 0 < rβ := hβ0 s hβs
      obtain ⟨z, hz, hPz⟩ := hψsupp (subset_tsupport _ hψs)
      have hsS : s ∈ S := hRS (mem_closedBall.2 (by linarith))
      have hw : p z * a = p s := by
        have e : P z * x⁻¹ = P s := by rw [hPz]; group
        have := congrArg (fun y : G => (((y : G) : 𝔸ˣ) : 𝔸)) e
        simpa only [Subgroup.coe_mul, Units.val_mul, hPv] using this
      have hzU : z ∈ U := ⟨hz, by
        show dist (p z * a) 1 < δ / 2
        rw [hw]; linarith [hps s hsr]⟩
      apply hs
      refine ⟨z, hzU, ?_⟩
      show Ψ (logCoord b (p z * a)) = s
      rw [hw]; exact hleft s hsS
    have hR : ∫ z in U, |(fderiv ℝ Λx z).det| • ((β (Λx z) : ℂ) * ψ₀ (P (Λx z) * x)) =
        ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ (a, z) : ℂ) := by
      rw [← integral_indicator hUo.measurableSet, ← integral_indicator measurableSet_ball]
      congr 1; funext z
      by_cases hzb : z ∈ ball (0 : Fin d → ℝ) r
      · rw [indicator_of_mem hzb]
        by_cases hzU : z ∈ U
        · rw [indicator_of_mem hzU]
          have hq := hUOg z hzU
          have hJpos : 0 < J (a, z) := hq.2
          have hdet : |(fderiv ℝ Λx z).det| = J (a, z) := abs_of_pos hJpos
          rw [hdet, hΛxP z hzU, show P z * x⁻¹ * x = P z by group]
          show J (a, z) • ((β (Λ (a, z)) : ℂ) * ψ₀ (P z)) =
            ψ₀ (P z) * (((θ z * χ (p z * a)) • (β (Λ (a, z)) * J (a, z)) : ℝ) : ℂ)
          by_cases hβz : β (Λ (a, z)) = 0
          · rw [hβz]; simp
          · have hs := hβ0 _ hβz
            have hpv : p (Λ (a, z)) = p z * a := by
              have := congrArg (fun y : G => (((y : G) : 𝔸ˣ) : 𝔸)) (hΛxP z hzU)
              simpa only [Subgroup.coe_mul, Units.val_mul, hPv] using this
            have hχ : χ (p z * a) = 1 := hχ1 _ (by rw [← hpv]; exact hps _ hs)
            rw [hχ, hθ1 z hzb, Complex.real_smul, smul_eq_mul]
            push_cast; ring
        · rw [indicator_of_notMem hzU]
          have hnot : ¬ dist (p z * a) 1 < δ / 2 := fun h' => hzU ⟨hzb, h'⟩
          have hχ : χ (p z * a) = 0 := by
            by_contra hne; exact hnot (hχ0 _ hne)
          show 0 = ψ₀ (P z) * (((θ z * χ (p z * a)) • (β (Λ (a, z)) * J (a, z)) : ℝ) : ℂ)
          rw [hχ]; simp
      · rw [indicator_of_notMem hzb, indicator_of_notMem (fun h' => hzb h'.1)]
    rw [← hL, hcov, hR]
  have hβint : 0 < ∫ s, β s := β.integral_pos
  refine ⟨r, fun z => D z / ∫ s, β s, c, Wc, hr, hDs.div_const _,
    fun z hz => div_pos (hDpos z hz) hβint, hWco, ?_, hPcW, ?_, ?_⟩
  · intro z hz
    have hzS : z ∈ S := hRS (mem_closedBall.2 (by have := mem_ball.1 hz; linarith))
    exact ⟨hPW z hzS, hcP z hzS⟩
  · intro g hg
    set gv : 𝔸 := (((g : G) : 𝔸ˣ) : 𝔸) with hgv
    have h1 : ContDiffAt ℝ ∞ (fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0 :=
      (contDiff_const.mul ((contDiff_exp 𝔸).comp 𝔤.subtypeL.contDiff)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (logCoord b) gv :=
      (contDiffOn_logCoord b).contDiffAt
        ((expPartialHomeomorph 𝔸).open_target.mem_nhds (h.nhdOne_subset_target hg.1))
    have h3 : ContDiffAt ℝ ∞ Ψ (logCoord b gv) := hΨ.contDiffAt (hTo.mem_nhds hg.2)
    have h0 : (fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0 = gv := by simp
    have h2' : ContDiffAt ℝ ∞ (logCoord b) ((fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0) := by
      rw [h0]; exact h2
    have h21 := h2'.comp (0 : 𝔤) h1
    have h3' : ContDiffAt ℝ ∞ Ψ ((logCoord b ∘ fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0) := by
      show ContDiffAt ℝ ∞ Ψ (logCoord b ((fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0))
      rw [h0]; exact h3
    have h321 := h3'.comp (0 : 𝔤) h21
    refine h321.congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)
    show Ψ (logCoord b (((g * h.expG Y : G) : 𝔸ˣ) : 𝔸)) = Ψ (logCoord b (gv * exp (Y : 𝔸)))
    rw [Subgroup.coe_mul, Units.val_mul, coe_expG]
  · intro ψ₀ hψc hψs hψsupp
    have hΘs : HasCompactSupport (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
        Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z)) := by
      refine HasCompactSupport.intro (hX₀.prod (isCompact_closedBall (0 : Fin d → ℝ) (2 * r))) ?_
      intro q hq
      by_contra hne
      obtain ⟨h1, h2⟩ := hsuppx q.1 q.2 hne
      exact hq ⟨h1, mem_closedBall.2 h2.le⟩
    have hmain : ((∫ s, β s : ℝ) : ℂ) * ∫ y, ψ₀ y ∂μ =
        ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (D z : ℂ) :=
      integral_mul_integral_eq_setIntegral_of_forall μ hPc β.continuous β.hasCompactSupport
        (Θ := fun x z => Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z))
        (hΞc.continuous.comp ((hu_c.comp continuous_fst).prodMk continuous_snd)) hΘs
        measurableSet_ball hψc hψs (hC ψ₀ hψsupp)
    have hβne : ((∫ s, β s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβint.ne'
    have e3 : ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (((D z / ∫ s, β s) : ℝ) : ℂ) =
        ((∫ s, β s : ℝ) : ℂ)⁻¹ * ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (D z : ℂ) := by
      rw [← integral_const_mul]
      congr 1; funext z
      push_cast
      field_simp
    show ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (((D z / ∫ s, β s) : ℝ) : ℂ)
    rw [e3, ← hmain, ← mul_assoc, inv_mul_cancel₀ hβne, one_mul]

end IsExpLieAlgebra

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

/-- **Smooth kernels on `ℝᵈ` are pull-backs of test functions on `G`.** There is `ε > 0` such that for
`δ ≤ ε` every smooth `K` on `ℝᵈ` supported in the closed ball `B̄(0, δ)` comes from a smooth
compactly supported `κ` on `G`, supported in `P (B̄(0, δ))`, with
`∫ κ φ dμ = ∫ K(t) φ(P t) dt` for every continuous `φ`: take `κ = (K / ρ) ∘ c` on `W`. -/
theorem exists_smooth_density_prodExp [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ δ ≤ ε, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 δ →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ h.prodExp (⇑b) '' closedBall 0 δ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩ := h.exists_haar_density_prodExp μ b
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  refine ⟨r / 2, by positivity, fun δ hδ K hK hKs => ?_⟩
  have hεr : closedBall (0 : Fin d → ℝ) δ ⊆ ball 0 r :=
    closedBall_subset_ball (by linarith)
  set C := P '' closedBall (0 : Fin d → ℝ) δ with hCdef
  have hCc : IsCompact C := (isCompact_closedBall _ _).image hPc
  let κ : G → ℂ := W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)
  have hκC : ∀ y, y ∉ C → κ y = 0 := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hz : c y ∉ closedBall (0 : Fin d → ℝ) δ := fun hz => hy ⟨c y, hz, hcP y hyW⟩
      have : K (c y) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')
      simp [κ, indicator_of_mem hyW, this]
    · simp [κ, indicator_of_notMem hyW]
  have hκsupp : tsupport κ ⊆ C :=
    closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed
  have hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := hPW z hz
    have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
    simp only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]
    field_simp
  have hsmooth : (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) := by
    intro g
    rw [h.contMDiffAt_iff_expG]
    have hcont : Continuous (fun Y : 𝔤 => g * h.expG Y) :=
      continuous_const.mul h.continuous_expG
    have hg0 : g * h.expG 0 = g := by rw [h.expG_zero, mul_one]
    by_cases hg : g ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hg
      have hz₀r : z₀ ∈ ball (0 : Fin d → ℝ) r := hεr hz₀
      obtain ⟨hgW, hcg⟩ := hPW z₀ hz₀r
      have hev : (fun Y : 𝔤 => κ (P z₀ * h.expG Y)) =ᶠ[𝓝 0]
          fun Y => K (c (P z₀ * h.expG Y)) * (((ρ (c (P z₀ * h.expG Y)))⁻¹ : ℝ) : ℂ) := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), P z₀ * h.expG Y ∈ W := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hW.mem_nhds hgW)
        filter_upwards [this] with Y hY
        simp [κ, indicator_of_mem hY]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hc0 := hc (P z₀) hgW
      have hρ0 : ρ (c (P z₀ * h.expG 0)) ≠ 0 := by
        rw [hg0, hcg]; exact (hρpos z₀ hz₀r).ne'
      exact (hK.contDiffAt.comp _ hc0).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ ((hρ.contDiffAt.comp _ hc0).inv hρ0))
    · have hev : (fun Y : 𝔤 => κ (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), g * h.expG Y ∈ Cᶜ := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hCc.isClosed.isOpen_compl.mem_nhds hg)
        filter_upwards [this] with Y hY
        exact hκC _ hY
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hκc : Continuous κ := by
    let := h.chartedSpace
    exact hsmooth.continuous
  refine ⟨κ, hsmooth, HasCompactSupport.intro hCc hκC, hκsupp, fun φ hφ => ?_⟩
  have hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r :=
    (tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))
  rw [hint (fun y => κ y * φ y) (hκc.mul hφ)
    ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t))
    (s := ball (0 : Fin d → ℝ) r) fun z hz => by
      have : K z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))
      simp [this]]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [mul_right_comm, hκW z hz]

end IsExpLieAlgebra

end Langlands.LinearLieGroup
