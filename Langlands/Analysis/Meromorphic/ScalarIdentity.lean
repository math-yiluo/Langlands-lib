import Langlands.Analysis.Meromorphic.LinearCoordinates
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Tactic.Ring

/-! # Scalar meromorphic uniqueness

The identity principle and arithmetic for scalar functions with the local
holomorphic denominators of `IsMeromorphicOn`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {U V W : Set E}

/-- For scalar functions on a complex normed space, weak holomorphy is complex
Fréchet differentiability. -/
theorem isHolomorphicOn_iff_differentiableOn_scalar :
    IsHolomorphicOn 𝓘(ℂ, E) f U ↔ DifferentiableOn ℂ f U := by
  constructor
  · intro hf
    simpa using (hf (ContinuousLinearMap.id ℂ ℂ)).differentiableOn
  · intro hf μ
    exact (μ.differentiable.comp_differentiableOn hf).mdifferentiableOn

private theorem eqOn_zero_of_convex (hf : DifferentiableOn ℂ f W)
    (hW : IsOpen W) (hc : Convex ℝ W) (hV : IsOpen V) (hVW : V ⊆ W)
    (hne : V.Nonempty) (hzero : EqOn f 0 V) : EqOn f 0 W := by
  obtain ⟨x, hx⟩ := hne
  intro y hy
  let line : ℂ → E := fun t => t • (y - x) + x
  have hline : Differentiable ℂ line :=
    (differentiable_id.smul_const (y - x)).add_const x
  have h0 : line 0 = x := by simp [line]
  have h1 : line 1 = y := by simp [line]
  have hpre : Convex ℝ (line ⁻¹' W) := by
    let L : ℂ →ₗ[ℝ] E := ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (y - x)).restrictScalars ℝ
    exact (hc.translate_preimage_left x).linear_preimage L
  have hslice := (hf.comp hline.differentiableOn (mapsTo_preimage line W)).analyticOnNhd
    (hW.preimage hline.continuous)
  have hnear : f ∘ line =ᶠ[𝓝 0] 0 := by
    filter_upwards [(hV.preimage hline.continuous).mem_nhds (show line 0 ∈ V by rwa [h0])]
      with t ht
    exact hzero ht
  simpa [Function.comp_def, h1] using
    hslice.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre.isPreconnected
      (show line 0 ∈ W by rw [h0]; exact hVW hx) hnear (show line 1 ∈ W by rwa [h1])

/-- A scalar holomorphic function on a connected open set that vanishes on a
nonempty open subset vanishes on the whole set. -/
theorem differentiableOn_eqOn_zero_of_isPreconnected (hf : DifferentiableOn ℂ f W)
    (hW : IsOpen W) (hc : IsPreconnected W) (hV : IsOpen V) (hVW : V ⊆ W)
    (hne : V.Nonempty) (hzero : EqOn f 0 V) : EqOn f 0 W := by
  let S := interior (W ∩ {x | f x = 0})
  have hVS : V ⊆ S := hV.subset_interior_iff.mpr fun x hx => ⟨hVW hx, hzero hx⟩
  have hWS : W ⊆ S := hc.subset_of_closure_inter_subset isOpen_interior
    (hne.mono fun x hx => ⟨hVW hx, hVS hx⟩) (by
      rintro x ⟨hxS, hxW⟩
      obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp hW x hxW
      have hBne := mem_closure_iff.mp hxS _ Metric.isOpen_ball (Metric.mem_ball_self hr)
      have hBzero := eqOn_zero_of_convex (hf.mono hB) Metric.isOpen_ball (convex_ball x r)
        (Metric.isOpen_ball.inter isOpen_interior) inter_subset_left hBne
        (fun y hy => (interior_subset hy.2).2)
      have hBS : Metric.ball x r ⊆ S :=
        Metric.isOpen_ball.subset_interior_iff.mpr fun y hy => ⟨hB hy, hBzero hy⟩
      exact hBS (Metric.mem_ball_self hr))
  exact fun x hx => (interior_subset (hWS hx)).2

private theorem nonzero_somewhere (hf : DifferentiableOn ℂ f W)
    (hW : IsOpen W) (hc : IsPreconnected W) (hnz : ∃ x ∈ W, f x ≠ 0)
    (hV : IsOpen V) (hVW : V ⊆ W) (hne : V.Nonempty) : ∃ x ∈ V, f x ≠ 0 := by
  by_contra! hzero
  obtain ⟨x, hx, hfx⟩ := hnz
  exact hfx (differentiableOn_eqOn_zero_of_isPreconnected hf hW hc hV hVW hne hzero hx)

private theorem eqOn_zero_of_open (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hV : IsOpen V) (hne : V.Nonempty) (hzero : EqOn f 0 (V ∩ U)) : EqOn f 0 U := by
  rcases hf with ⟨hU, hdU, hf, hlocal⟩
  let S := interior {x | x ∈ U → f x = 0}
  have hVS : V ⊆ S := hV.subset_interior_iff.mpr fun x hx hxU => hzero ⟨hx, hxU⟩
  have hclosed : IsClosed S := isClosed_of_closure_subset (by
    intro x hxS
    obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hlocal x
    have hd' := hd.differentiableOn
    have hn' := isHolomorphicOn_iff_differentiableOn_scalar.mp hn
    have hWS : IsOpen (W ∩ S) := hW.inter isOpen_interior
    have hWSne := mem_closure_iff.mp hxS W hW hxW
    have hnzero : EqOn n 0 ((W ∩ S) ∩ U) := by
      rintro y ⟨⟨hyW, hyS⟩, hyU⟩
      rw [← hdf y ⟨hyU, hyW⟩, interior_subset hyS hyU, smul_zero]
      rfl
    have hnWS := hnzero.of_subset_closure (hn'.continuousOn.mono inter_subset_left)
      continuousOn_const inter_subset_left (by
        simpa only [inter_comm] using hdU.open_subset_closure_inter hWS)
    have hnW := differentiableOn_eqOn_zero_of_isPreconnected hn' hW hcW.2 hWS
      inter_subset_left hWSne hnWS
    apply (hW.subset_interior_iff.mpr ?_) hxW
    intro y hyW hyU
    by_contra hfy
    let O := (W ∩ U) ∩ f ⁻¹' ({0}ᶜ : Set ℂ)
    have hO : IsOpen O := ((isHolomorphicOn_iff_differentiableOn_scalar.mp hf).continuousOn.mono
      (inter_subset_right : W ∩ U ⊆ U)).isOpen_inter_preimage (hW.inter hU)
        isClosed_singleton.isOpen_compl
    obtain ⟨z, hz, hzd⟩ := nonzero_somewhere hd' hW hcW.2 hdnz hO
      (fun _ hz => hz.1.1) ⟨y, ⟨hyW, hyU⟩, hfy⟩
    have ⟨⟨hzW, hzU⟩, hzf⟩ := hz
    have hprod : d z * f z = 0 := (hdf z ⟨hzU, hzW⟩).trans (hnW hzW)
    exact (mul_ne_zero hzd hzf) hprod)
  have hS : S = univ := IsClopen.eq_univ ⟨hclosed, isOpen_interior⟩ (hne.mono hVS)
  intro x hx
  have hxS : x ∈ S := hS.symm ▸ mem_univ x
  have hvanish : x ∈ U → f x = 0 := interior_subset hxS
  exact hvanish hx

private theorem exists_local_presentations (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hg : IsMeromorphicOn 𝓘(ℂ, E) g V) (x : E) :
    ∃ B : Set E, IsOpen B ∧ IsConnected B ∧ x ∈ B ∧
      ∃ d e n m : E → ℂ, DifferentiableOn ℂ d B ∧ DifferentiableOn ℂ e B ∧
        (∃ y ∈ B, d y * e y ≠ 0) ∧ DifferentiableOn ℂ n B ∧ DifferentiableOn ℂ m B ∧
        EqOn (d * f) n ((U ∩ V) ∩ B) ∧ EqOn (e * g) m ((U ∩ V) ∩ B) := by
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  obtain ⟨Z, hZ, hcZ, hxZ, e, m, he, henz, hm, heg⟩ := hg.2.2.2 x
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp (hW.inter hZ) x ⟨hxW, hxZ⟩
  let B := Metric.ball x r
  have hBo : IsOpen B := Metric.isOpen_ball
  have hxB : x ∈ B := Metric.mem_ball_self hr
  have hBW : B ⊆ W := fun _ hy => (hB hy).1
  have hBZ : B ⊆ Z := fun _ hy => (hB hy).2
  have hdB := hd.differentiableOn.mono hBW
  have heB := he.differentiableOn.mono hBZ
  obtain ⟨y, hy, hyd⟩ := nonzero_somewhere hd.differentiableOn hW hcW.2 hdnz
    hBo hBW ⟨x, hxB⟩
  let O := B ∩ d ⁻¹' ({0}ᶜ : Set ℂ)
  have hO : IsOpen O := hdB.continuousOn.isOpen_inter_preimage hBo
    isClosed_singleton.isOpen_compl
  obtain ⟨z, hz, hze⟩ := nonzero_somewhere he.differentiableOn hZ hcZ.2 henz
    hO (fun _ hz => hBZ hz.1) ⟨y, hy, hyd⟩
  exact ⟨B, hBo, (convex_ball x r).isConnected ⟨x, hxB⟩, hxB, d, e, n, m, hdB, heB,
    ⟨z, hz.1, mul_ne_zero hz.2 hze⟩, (isHolomorphicOn_iff_differentiableOn_scalar.mp hn).mono hBW,
    (isHolomorphicOn_iff_differentiableOn_scalar.mp hm).mono hBZ,
    fun y hy => hdf y ⟨hy.1.1, hBW hy.2⟩, fun y hy => heg y ⟨hy.1.2, hBZ hy.2⟩⟩

/-- A scalar meromorphic function remains meromorphic on a smaller open dense
holomorphy domain. -/
theorem IsMeromorphicOn.restrict_domain (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hV : IsOpen V) (hdV : Dense V) (hVU : V ⊆ U) : IsMeromorphicOn 𝓘(ℂ, E) f V := by
  refine ⟨hV, hdV, fun μ => (hf.2.2.1 μ).mono hVU, fun x => ?_⟩
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  exact ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, fun y hy => hdf y ⟨hVU hy.1, hy.2⟩⟩

/-- Scalar constants are meromorphic with full holomorphy domain. -/
theorem isMeromorphicOn_const (c : ℂ) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun _ : E => c) univ := by
  have hc : DifferentiableOn ℂ (fun _ : E => c) univ := differentiableOn_const c
  have h1 : DifferentiableOn ℂ (fun _ : E => (1 : ℂ)) univ := differentiableOn_const 1
  exact ⟨isOpen_univ, dense_univ, isHolomorphicOn_iff_differentiableOn_scalar.mpr hc,
    fun x => ⟨univ, isOpen_univ, isConnected_univ, mem_univ x, fun _ => 1, fun _ => c,
      h1.mdifferentiableOn, ⟨x, mem_univ x, one_ne_zero⟩,
      isHolomorphicOn_iff_differentiableOn_scalar.mpr hc, fun _ _ => one_smul _ _⟩⟩

/-- Addition of scalar meromorphic functions on their common holomorphy domain. -/
theorem IsMeromorphicOn.add (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hg : IsMeromorphicOn 𝓘(ℂ, E) g V) : IsMeromorphicOn 𝓘(ℂ, E) (f + g) (U ∩ V) := by
  refine ⟨hf.1.inter hg.1, hf.2.1.inter_of_isOpen_right hg.2.1 hg.1,
    isHolomorphicOn_iff_differentiableOn_scalar.mpr
      (((isHolomorphicOn_iff_differentiableOn_scalar.mp hf.2.2.1).mono inter_subset_left).add
        ((isHolomorphicOn_iff_differentiableOn_scalar.mp hg.2.2.1).mono inter_subset_right)), ?_⟩
  intro x
  obtain ⟨B, hB, hcB, hxB, d, e, n, m, hd, he, hne, hn, hm, hdf, heg⟩ :=
    exists_local_presentations hf hg x
  refine ⟨B, hB, hcB, hxB, d * e, e * n + d * m, (hd.mul he).mdifferentiableOn,
    hne, isHolomorphicOn_iff_differentiableOn_scalar.mpr ((he.mul hn).add (hd.mul hm)), ?_⟩
  intro y hy
  change d y * e y * (f y + g y) = e y * n y + d y * m y
  calc
    _ = e y * (d * f) y + d y * (e * g) y := by simp only [Pi.mul_apply]; ring
    _ = _ := by rw [hdf hy, heg hy]

/-- Multiplication of scalar meromorphic functions on their common holomorphy domain. -/
theorem IsMeromorphicOn.mul (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hg : IsMeromorphicOn 𝓘(ℂ, E) g V) : IsMeromorphicOn 𝓘(ℂ, E) (f * g) (U ∩ V) := by
  refine ⟨hf.1.inter hg.1, hf.2.1.inter_of_isOpen_right hg.2.1 hg.1,
    isHolomorphicOn_iff_differentiableOn_scalar.mpr
      (((isHolomorphicOn_iff_differentiableOn_scalar.mp hf.2.2.1).mono inter_subset_left).mul
        ((isHolomorphicOn_iff_differentiableOn_scalar.mp hg.2.2.1).mono inter_subset_right)), ?_⟩
  intro x
  obtain ⟨B, hB, hcB, hxB, d, e, n, m, hd, he, hne, hn, hm, hdf, heg⟩ :=
    exists_local_presentations hf hg x
  refine ⟨B, hB, hcB, hxB, d * e, n * m, (hd.mul he).mdifferentiableOn, hne,
    isHolomorphicOn_iff_differentiableOn_scalar.mpr (hn.mul hm), ?_⟩
  intro y hy
  change d y * e y * (f y * g y) = n y * m y
  calc
    _ = (d * f) y * (e * g) y := by simp only [Pi.mul_apply]; ring
    _ = _ := by rw [hdf hy, heg hy]

/-- Negation preserves scalar meromorphy. -/
theorem IsMeromorphicOn.neg (hf : IsMeromorphicOn 𝓘(ℂ, E) f U) :
    IsMeromorphicOn 𝓘(ℂ, E) (-f) U := by
  refine ⟨hf.1, hf.2.1, isHolomorphicOn_iff_differentiableOn_scalar.mpr
    (isHolomorphicOn_iff_differentiableOn_scalar.mp hf.2.2.1).neg, ?_⟩
  intro x
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  refine ⟨W, hW, hcW, hxW, d, -n, hd, hdnz, isHolomorphicOn_iff_differentiableOn_scalar.mpr
    (isHolomorphicOn_iff_differentiableOn_scalar.mp hn).neg, ?_⟩
  intro y hy
  change d y * -f y = -n y
  rw [mul_neg, ← hdf y hy]
  rfl

/-- A finite sum of scalar meromorphic functions with a common open dense
holomorphy domain is meromorphic there. -/
theorem IsMeromorphicOn.sum {ι : Type*} (s : Finset ι) {a : ι → E → ℂ}
    (hU : IsOpen U) (hdU : Dense U) (ha : ∀ i ∈ s, IsMeromorphicOn 𝓘(ℂ, E) (a i) U) :
    IsMeromorphicOn 𝓘(ℂ, E) (∑ i ∈ s, a i) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact (isMeromorphicOn_const (E := E) 0).restrict_domain hU hdU (subset_univ U)
  | @insert i t hi ih =>
    have hai := ha i (Finset.mem_insert_self i t)
    have hat := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi]
    simpa only [inter_self] using hai.add hat

/-- Scalar meromorphic functions agreeing on the part of a nonempty open set
in their common holomorphy domain agree on the whole common domain. -/
theorem IsMeromorphicOn.eqOn_of_eqOn_open (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hg : IsMeromorphicOn 𝓘(ℂ, E) g V) (hW : IsOpen W) (hne : W.Nonempty)
    (heq : EqOn f g (W ∩ (U ∩ V))) : EqOn f g (U ∩ V) := by
  have hzero : EqOn (f + -g) 0 (W ∩ (U ∩ V)) := by
    intro x hx
    change f x + -g x = 0
    rw [heq hx, add_neg_cancel]
  intro x hx
  have h := eqOn_zero_of_open (hf.add hg.neg) hW hne hzero hx
  change f x + -g x = 0 at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

section Coordinates

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  {a b : X → ℂ} {S T : Set X}

/-- Scalar meromorphy in linear coordinates is preserved by a linear equivalence
of parameter spaces. -/
theorem IsMeromorphicInCoordinatesOn.comp_linearEquiv {h : Y → ℂ} {Q : Set Y}
    (hh : IsMeromorphicInCoordinatesOn h Q) (e : X ≃ₗ[ℂ] Y) :
    IsMeromorphicInCoordinatesOn (h ∘ e) (e ⁻¹' Q) := by
  let : FiniteDimensional ℂ Y := hh.1
  exact ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    fun n c => hh.2 n (c.trans e)⟩

/-- The product of two scalar meromorphic functions in linear coordinates is
meromorphic on the intersection of their holomorphy domains. -/
theorem IsMeromorphicInCoordinatesOn.mul (ha : IsMeromorphicInCoordinatesOn a S)
    (hb : IsMeromorphicInCoordinatesOn b T) :
    IsMeromorphicInCoordinatesOn (a * b) (S ∩ T) :=
  ⟨ha.1, fun n e => (ha.2 n e).mul (hb.2 n e)⟩

/-- Constants are meromorphic in linear coordinates on the full parameter space. -/
theorem isMeromorphicInCoordinatesOn_const [FiniteDimensional ℂ X] (c : ℂ) :
    IsMeromorphicInCoordinatesOn (fun _ : X => c) univ :=
  ⟨inferInstance, fun _ _ => isMeromorphicOn_const c⟩

/-- A finite sum is meromorphic in linear coordinates on a common holomorphy
domain that is open and dense in every chart. -/
theorem IsMeromorphicInCoordinatesOn.sum [FiniteDimensional ℂ X] {ι : Type*}
    (s : Finset ι) {h : ι → X → ℂ}
    (hS : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' S) ∧ Dense (e ⁻¹' S))
    (hh : ∀ i ∈ s, IsMeromorphicInCoordinatesOn (h i) S) :
    IsMeromorphicInCoordinatesOn (∑ i ∈ s, h i) S := by
  refine ⟨inferInstance, fun n e => ?_⟩
  convert IsMeromorphicOn.sum s (hS n e).1 (hS n e).2 (fun i hi => (hh i hi).2 n e) using 1
  ext x
  simp only [Function.comp_apply, Finset.sum_apply]

/-- Scalar meromorphic functions in linear coordinates that agree on an open
patch in one chart agree throughout their common holomorphy domain. -/
theorem IsMeromorphicInCoordinatesOn.eqOn_of_eqOn_open
    (ha : IsMeromorphicInCoordinatesOn a S) (hb : IsMeromorphicInCoordinatesOn b T)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] X) {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hne : O.Nonempty) (heq : EqOn (a ∘ e) (b ∘ e) (O ∩ (e ⁻¹' (S ∩ T)))) :
    EqOn a b (S ∩ T) := by
  intro x hx
  have hy : e.symm x ∈ e ⁻¹' (S ∩ T) := by simpa using hx
  simpa using (ha.2 n e).eqOn_of_eqOn_open (hb.2 n e) hO hne heq hy

end Coordinates

end Langlands.Analysis.Meromorphic
