import Langlands.Global.AdelicIntertwiningCocycleStatement
import Langlands.Global.AdelicEisensteinFunctionalEquationStatement
import Langlands.Global.AdelicEisensteinPointwiseContinuationStatement
import Langlands.Global.AdelicEisensteinGenericInjectivityStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Ring

/-! # Reduction of the cocycle relation of intertwining operators

Bernstein–Lapid, §8.6: the cocycle relation `M(w'w, λ) = M(w', wλ) ∘ M(w, λ)`
(Theorem 2.3 (5)) follows from the functional equation (Theorem 2.3 (4)), the
meromorphic continuation of intertwining operators (Theorem 2.3 (3)), the pointwise
meromorphic continuation of Eisenstein series (Theorem 2.3 (1)) and the generic injectivity
(8.4) of `φ ↦ E(φ, λ)` on finite-dimensional spaces of automorphic forms.

The private sections on scalar meromorphic functions, Weyl parameters and regular regions
reproduce helper lemmas written by Worker 587 (Task 5502 draft); they are private here so that a
later publication of the originals causes no name clash. Lemmas marked as new are by Worker 86. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

/-! ## Scalar meromorphic functions (after Worker 587) -/

namespace Langlands.Analysis.Meromorphic
open Set Filter
open scoped Manifold _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {U V W : Set E}

/-- For scalar functions on a complex normed space, weak holomorphy is complex
Fréchet differentiability. -/
private theorem isHolomorphicOn_iff_differentiableOn :
    IsHolomorphicOn 𝓘(ℂ, E) f U ↔ DifferentiableOn ℂ f U := by
  constructor
  · intro hf
    simpa using (hf (ContinuousLinearMap.id ℂ ℂ)).differentiableOn
  · intro hf mu
    exact (mu.differentiable.comp_differentiableOn hf).mdifferentiableOn

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
private theorem differentiableOn_eqOn_zero_of_isPreconnected (hf : DifferentiableOn ℂ f W)
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
    have hn' := isHolomorphicOn_iff_differentiableOn.mp hn
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
    have hO : IsOpen O := ((isHolomorphicOn_iff_differentiableOn.mp hf).continuousOn.mono
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
    ⟨z, hz.1, mul_ne_zero hz.2 hze⟩, (isHolomorphicOn_iff_differentiableOn.mp hn).mono hBW,
    (isHolomorphicOn_iff_differentiableOn.mp hm).mono hBZ,
    fun y hy => hdf y ⟨hy.1.1, hBW hy.2⟩, fun y hy => heg y ⟨hy.1.2, hBZ hy.2⟩⟩

/-- A scalar meromorphic function remains meromorphic on a smaller open dense
holomorphy domain. -/
private theorem IsMeromorphicOn.restrict_domain (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hV : IsOpen V) (hdV : Dense V) (hVU : V ⊆ U) : IsMeromorphicOn 𝓘(ℂ, E) f V := by
  refine ⟨hV, hdV, fun mu => (hf.2.2.1 mu).mono hVU, fun x => ?_⟩
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  exact ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, fun y hy => hdf y ⟨hVU hy.1, hy.2⟩⟩

/-- Scalar constants are meromorphic with full holomorphy domain. -/
private theorem isMeromorphicOn_const (c : ℂ) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun _ : E => c) univ := by
  have hc : DifferentiableOn ℂ (fun _ : E => c) univ := differentiableOn_const c
  have h1 : DifferentiableOn ℂ (fun _ : E => (1 : ℂ)) univ := differentiableOn_const 1
  exact ⟨isOpen_univ, dense_univ, isHolomorphicOn_iff_differentiableOn.mpr hc,
    fun x => ⟨univ, isOpen_univ, isConnected_univ, mem_univ x, fun _ => 1, fun _ => c,
      h1.mdifferentiableOn, ⟨x, mem_univ x, one_ne_zero⟩,
      isHolomorphicOn_iff_differentiableOn.mpr hc, fun _ _ => one_smul _ _⟩⟩

/-- Addition of scalar meromorphic functions on their common holomorphy domain. -/
private theorem IsMeromorphicOn.add (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hg : IsMeromorphicOn 𝓘(ℂ, E) g V) : IsMeromorphicOn 𝓘(ℂ, E) (f + g) (U ∩ V) := by
  refine ⟨hf.1.inter hg.1, hf.2.1.inter_of_isOpen_right hg.2.1 hg.1,
    isHolomorphicOn_iff_differentiableOn.mpr
      (((isHolomorphicOn_iff_differentiableOn.mp hf.2.2.1).mono inter_subset_left).add
        ((isHolomorphicOn_iff_differentiableOn.mp hg.2.2.1).mono inter_subset_right)), ?_⟩
  intro x
  obtain ⟨B, hB, hcB, hxB, d, e, n, m, hd, he, hne, hn, hm, hdf, heg⟩ :=
    exists_local_presentations hf hg x
  refine ⟨B, hB, hcB, hxB, d * e, e * n + d * m, (hd.mul he).mdifferentiableOn,
    hne, isHolomorphicOn_iff_differentiableOn.mpr ((he.mul hn).add (hd.mul hm)), ?_⟩
  intro y hy
  change d y * e y * (f y + g y) = e y * n y + d y * m y
  calc
    _ = e y * (d * f) y + d y * (e * g) y := by simp only [Pi.mul_apply]; ring
    _ = _ := by rw [hdf hy, heg hy]

/-- Multiplication of scalar meromorphic functions on their common holomorphy domain. -/
private theorem IsMeromorphicOn.mul (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
    (hg : IsMeromorphicOn 𝓘(ℂ, E) g V) : IsMeromorphicOn 𝓘(ℂ, E) (f * g) (U ∩ V) := by
  refine ⟨hf.1.inter hg.1, hf.2.1.inter_of_isOpen_right hg.2.1 hg.1,
    isHolomorphicOn_iff_differentiableOn.mpr
      (((isHolomorphicOn_iff_differentiableOn.mp hf.2.2.1).mono inter_subset_left).mul
        ((isHolomorphicOn_iff_differentiableOn.mp hg.2.2.1).mono inter_subset_right)), ?_⟩
  intro x
  obtain ⟨B, hB, hcB, hxB, d, e, n, m, hd, he, hne, hn, hm, hdf, heg⟩ :=
    exists_local_presentations hf hg x
  refine ⟨B, hB, hcB, hxB, d * e, n * m, (hd.mul he).mdifferentiableOn, hne,
    isHolomorphicOn_iff_differentiableOn.mpr (hn.mul hm), ?_⟩
  intro y hy
  change d y * e y * (f y * g y) = n y * m y
  calc
    _ = (d * f) y * (e * g) y := by simp only [Pi.mul_apply]; ring
    _ = _ := by rw [hdf hy, heg hy]

/-- Negation preserves scalar meromorphy. -/
private theorem IsMeromorphicOn.neg (hf : IsMeromorphicOn 𝓘(ℂ, E) f U) :
    IsMeromorphicOn 𝓘(ℂ, E) (-f) U := by
  refine ⟨hf.1, hf.2.1, isHolomorphicOn_iff_differentiableOn.mpr
    (isHolomorphicOn_iff_differentiableOn.mp hf.2.2.1).neg, ?_⟩
  intro x
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  refine ⟨W, hW, hcW, hxW, d, -n, hd, hdnz, isHolomorphicOn_iff_differentiableOn.mpr
    (isHolomorphicOn_iff_differentiableOn.mp hn).neg, ?_⟩
  intro y hy
  change d y * -f y = -n y
  rw [mul_neg, ← hdf y hy]
  rfl

/-- A finite sum of scalar meromorphic functions with a common open dense
holomorphy domain is meromorphic there. -/
private theorem IsMeromorphicOn.sum {κ : Type*} (s : Finset κ) {a : κ → E → ℂ}
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
private theorem IsMeromorphicOn.eqOn_of_eqOn_open (hf : IsMeromorphicOn 𝓘(ℂ, E) f U)
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
private theorem IsMeromorphicInCoordinatesOn.comp_linearEquiv {h : Y → ℂ} {Q : Set Y}
    (hh : IsMeromorphicInCoordinatesOn h Q) (e : X ≃ₗ[ℂ] Y) :
    IsMeromorphicInCoordinatesOn (h ∘ e) (e ⁻¹' Q) := by
  let : FiniteDimensional ℂ Y := hh.1
  exact ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    fun n c => hh.2 n (c.trans e)⟩

/-- The product of two scalar meromorphic functions in linear coordinates is
meromorphic on the intersection of their holomorphy domains. -/
private theorem IsMeromorphicInCoordinatesOn.mul (ha : IsMeromorphicInCoordinatesOn a S)
    (hb : IsMeromorphicInCoordinatesOn b T) :
    IsMeromorphicInCoordinatesOn (a * b) (S ∩ T) :=
  ⟨ha.1, fun n e => (ha.2 n e).mul (hb.2 n e)⟩

/-- Constants are meromorphic in linear coordinates on the full parameter space. -/
private theorem isMeromorphicInCoordinatesOn_const [FiniteDimensional ℂ X] (c : ℂ) :
    IsMeromorphicInCoordinatesOn (fun _ : X => c) univ :=
  ⟨inferInstance, fun _ _ => isMeromorphicOn_const c⟩

/-- A finite sum is meromorphic in linear coordinates on a common holomorphy
domain that is open and dense in every chart. -/
private theorem IsMeromorphicInCoordinatesOn.sum [FiniteDimensional ℂ X] {κ : Type*}
    (s : Finset κ) {h : κ → X → ℂ}
    (hS : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' S) ∧ Dense (e ⁻¹' S))
    (hh : ∀ i ∈ s, IsMeromorphicInCoordinatesOn (h i) S) :
    IsMeromorphicInCoordinatesOn (∑ i ∈ s, h i) S := by
  refine ⟨inferInstance, fun n e => ?_⟩
  convert IsMeromorphicOn.sum s (hS n e).1 (hS n e).2 (fun i hi => (hh i hi).2 n e) using 1
  ext x
  simp only [Function.comp_apply, Finset.sum_apply]

/-- Scalar meromorphic functions in linear coordinates that agree on an open
patch in one chart agree throughout their common holomorphy domain. -/
private theorem IsMeromorphicInCoordinatesOn.eqOn_of_eqOn_open
    (ha : IsMeromorphicInCoordinatesOn a S) (hb : IsMeromorphicInCoordinatesOn b T)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] X) {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hne : O.Nonempty) (heq : EqOn (a ∘ e) (b ∘ e) (O ∩ (e ⁻¹' (S ∩ T)))) :
    EqOn a b (S ∩ T) := by
  intro x hx
  have hy : e.symm x ∈ e ⁻¹' (S ∩ T) := by simpa using hx
  simpa using (ha.2 n e).eqOn_of_eqOn_open (hb.2 n e) hO hne heq hy

/-! The following domain lemmas are new in this module. -/

/-- A set of parameters is open and dense in every complex linear chart. -/
private def OpenDenseInCoordinates (S : Set X) : Prop :=
  ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' S) ∧ Dense (e ⁻¹' S)

/-- The holomorphy domain of a function meromorphic in linear coordinates is open and dense
in every chart. -/
private theorem IsMeromorphicInCoordinatesOn.openDense (ha : IsMeromorphicInCoordinatesOn a S) :
    OpenDenseInCoordinates S :=
  fun n e => ⟨(ha.2 n e).1, (ha.2 n e).2.1⟩

private theorem openDenseInCoordinates_univ : OpenDenseInCoordinates (univ : Set X) := by
  intro n e
  rw [preimage_univ]
  exact ⟨isOpen_univ, dense_univ⟩

private theorem OpenDenseInCoordinates.inter (hS : OpenDenseInCoordinates S)
    (hT : OpenDenseInCoordinates T) : OpenDenseInCoordinates (S ∩ T) := by
  intro n e
  rw [preimage_inter]
  exact ⟨(hS n e).1.inter (hT n e).1, (hS n e).2.inter_of_isOpen_left (hT n e).2 (hS n e).1⟩

private theorem OpenDenseInCoordinates.preimage {Q : Set Y} (hQ : OpenDenseInCoordinates Q)
    (W : X ≃ₗ[ℂ] Y) : OpenDenseInCoordinates (W ⁻¹' Q) :=
  fun n e => hQ n (e.trans W)

/-- Finite intersections of sets open and dense in every chart (Baire's theorem in each
chart). -/
private theorem OpenDenseInCoordinates.iInter {Idx : Type*} [Finite Idx] {S : Idx → Set X}
    (hS : ∀ i, OpenDenseInCoordinates (S i)) : OpenDenseInCoordinates (⋂ i, S i) := by
  intro n e
  rw [preimage_iInter]
  exact ⟨isOpen_iInter_of_finite fun i => (hS i n e).1,
    dense_iInter_of_isOpen (fun i => (hS i n e).1) fun i => (hS i n e).2⟩

/-- For a family of functions meromorphic on `S`, the set `⋂ _ : Idx, S` (which is `S` for a
nonempty index type and the whole space otherwise) is a common holomorphy domain that is open
and dense in every chart. -/
private theorem isMeromorphicInCoordinatesOn_iInter_const {Idx : Type*} {h : Idx → X → ℂ}
    (hh : ∀ i, IsMeromorphicInCoordinatesOn (h i) S) :
    (∀ i, IsMeromorphicInCoordinatesOn (h i) (⋂ _ : Idx, S)) ∧
      OpenDenseInCoordinates (⋂ _ : Idx, S) := by
  by_cases hI : Nonempty Idx
  · have := hI
    rw [iInter_const]
    exact ⟨hh, (hh hI.some).openDense⟩
  · rw [not_nonempty_iff] at hI
    rw [iInter_of_empty]
    exact ⟨fun i => isEmptyElim i, openDenseInCoordinates_univ⟩

/-- Multiplying by a constant keeps the holomorphy domain. -/
private theorem IsMeromorphicInCoordinatesOn.mul_const (ha : IsMeromorphicInCoordinatesOn a S)
    (c : ℂ) : IsMeromorphicInCoordinatesOn (fun x => a x * c) S := by
  let : FiniteDimensional ℂ X := ha.1
  have h := ha.mul (isMeromorphicInCoordinatesOn_const (X := X) c)
  rw [inter_univ] at h
  exact h

/-- A finite sum of functions meromorphic on `S` is meromorphic on `⋂ _ : Idx, S`. -/
private theorem IsMeromorphicInCoordinatesOn.sum_iInter [FiniteDimensional ℂ X] {Idx : Type*}
    [Fintype Idx] {h : Idx → X → ℂ} (hh : ∀ i, IsMeromorphicInCoordinatesOn (h i) S) :
    IsMeromorphicInCoordinatesOn (fun x => ∑ i, h i x) (⋂ _ : Idx, S) := by
  obtain ⟨hh', hS⟩ := isMeromorphicInCoordinatesOn_iInter_const hh
  convert IsMeromorphicInCoordinatesOn.sum Finset.univ hS (fun i _ => hh' i) using 1
  ext x
  simp only [Finset.sum_apply]

end Coordinates


end Langlands.Analysis.Meromorphic

/-! ## Weyl parameters are linear equivalences (after Worker 587) -/

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {P Q M M' : GroupScheme (Spec (CommRingCat.of F))}

private theorem characterRestrict_injective_of_levi {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) : Function.Injective (characterRestrict l) := by
  obtain ⟨U, i, hi, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l i) := hmul
  intro χ ψ h
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  have hfactor (θ : rationalCharacters P) :
      x ≫ θ.toMul.hom.hom = leviComponent l i x ≫ (characterRestrict l θ).toMul.hom.hom := by
    have htriv := hi.1.isUnipotent.comp_eq_one_of_isSplitTorus isSplitTorus_gm
      (i ≫ θ.toMul) T (radicalComponent l i x)
    simp only [Grp.comp_hom_hom] at htriv
    calc
      _ = ((leviComponent l i x ≫ l.hom.hom) *
          (radicalComponent l i x ≫ i.hom.hom)) ≫ θ.toMul.hom.hom :=
        congrArg (fun y : T ⟶ P.X => y ≫ θ.toMul.hom.hom)
          (leviComponent_mul_radicalComponent l i x).symm
      _ = _ := by
        simp only [MonObj.mul_comp, Category.assoc, htriv, mul_one,
          characterRestrict_apply, Grp.comp_hom_hom]
  rw [hfactor χ, hfactor ψ, h]

private theorem characterRestrict_rightInverse {L H : GroupScheme (Spec (CommRingCat.of F))}
    (j : L ⟶ H) (q : H ⟶ L) (hq : j ≫ q = 𝟙 L) :
    Function.RightInverse (characterRestrict q) (characterRestrict j) := by
  intro χ
  change ((characterRestrict j).comp (characterRestrict q)) χ = χ
  rw [← characterRestrict_comp, hq, characterRestrict_id]
  rfl

/-- Restriction to a rational Levi is bijective on rational characters. -/
private theorem characterRestrict_bijective_of_levi
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l) : Function.Bijective (characterRestrict l) := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  exact ⟨characterRestrict_injective_of_levi hl, (characterRestrict_rightInverse l π hπ).surjective⟩

private noncomputable def leviCharacterEquiv {L H : GroupScheme (Spec (CommRingCat.of F))}
    (j : L ⟶ H) (hj : IsRationalLeviSubgroup j) (q : H ⟶ L) (hq : j ≫ q = 𝟙 L) :
    rationalCharacters H ≃+ rationalCharacters L where
  toFun := characterRestrict j
  invFun := characterRestrict q
  left_inv χ := characterRestrict_injective_of_levi hj
    (characterRestrict_rightInverse j q hq (characterRestrict j χ))
  right_inv := characterRestrict_rightInverse j q hq
  map_add' := (characterRestrict j).map_add

private noncomputable def isoCharacterEquiv (c : M' ⟶ M) [IsIso c] :
    rationalCharacters M ≃+ rationalCharacters M' where
  toFun := characterRestrict c
  invFun := characterRestrict (inv c)
  left_inv := characterRestrict_rightInverse (inv c) c (IsIso.inv_hom_id c)
  right_inv := characterRestrict_rightInverse c (inv c) (IsIso.hom_inv_id c)
  map_add' := (characterRestrict c).map_add

/-- The Weyl parameter map is a complex linear equivalence. Its forward map
uses the indicated retraction of the target Levi. -/
private theorem exists_weylParameter_linearEquiv [NumberField F] (l : M ⟶ P) (l' : M' ⟶ Q)
    (hl : IsRationalLeviSubgroup l) (hl' : IsRationalLeviSubgroup l')
    (c : M' ⟶ M) [IsIso c] (π' : Q ⟶ M') (hπ' : l' ≫ π' = 𝟙 M') :
    ∃ e : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F Q,
      e.toLinearMap = weylParameter l c π' := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  let e := ((leviCharacterEquiv l hl π hπ).trans (isoCharacterEquiv c)).trans
    (leviCharacterEquiv l' hl' π' hπ').symm
  refine ⟨AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) e.toIntLinearEquiv, ?_⟩
  apply AlgebraTensorModule.ext
  intro s χ
  change s ⊗ₜ[ℤ] characterRestrict π' (characterRestrict c (characterRestrict l χ)) =
    weylParameter l c π' (s ⊗ₜ[ℤ] χ)
  simp only [weylParameter_tmul, characterRestrict_comp, AddMonoidHom.comp_apply]


end Langlands.Global.AdelicGroupPoints

/-! ## Regular regions are open and nonempty (after Worker 587) -/

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Set
open Langlands.Global.AdelicGroupPoints Langlands.Plancherel Langlands.LinearAlgebra

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

private theorem finite_unipotentRoots (hT : IsSplitTorus r.data.T.toGrp) :
    r.unipotentRoots.Finite :=
  ((hT.finite_positiveRelativeRoots r.data.i r.data.ν).image (r.data.f ≫ ·)).subset
    (fun _ h => h.2)

variable
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- The strict inequalities that define regular parameters give an open
region in every complex linear chart. -/
private theorem isOpen_regularParameter_inCoordinates (R : ℝ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    IsOpen {x | r.IsRegularParameter hA hT R (e x)} := by
  let : Finite r.unipotentRoots := (r.finite_unipotentRoots hT).to_subtype
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  let L (α : characterLattice A) : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    (B.flip ((1 : ℝ) ⊗ₜ[ℤ] α)).comp
      ((realParameterRestriction (a ≫ l)).comp
        ((parameterRealPart F P).comp (e.toLinearMap.restrictScalars ℝ)))
  have heq : {x | r.IsRegularParameter hA hT R (e x)} =
      ⋂ α : r.unipotentRoots, {x | R < L α x} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, Subtype.forall]
    rfl
  rw [heq]
  exact isOpen_iInter_of_finite (fun α => isOpen_lt continuous_const
    (L α).continuous_of_finiteDimensional)

private theorem parameterRealPart_surjective :
    Function.Surjective (parameterRealPart F P) := by
  let f : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
    AlgebraTensorModule.map Complex.ofRealCLM.toLinearMap LinearMap.id
  have hf : (parameterRealPart F P).comp f = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro s χ
    change (s : ℂ).re ⊗ₜ[ℤ] χ = s ⊗ₜ[ℤ] χ
    rw [Complex.ofReal_re]
  exact fun y => ⟨f y, LinearMap.congr_fun hf y⟩

private theorem realParameterRestriction_surjective
    (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    Function.Surjective (realParameterRestriction (F := F) (a ≫ l)) := by
  let f := (characterRestrict (a ≫ l)).toIntLinearMap
  have hf : Function.Surjective (f.baseChange ℚ) := by
    have hs₁ := LinearMap.baseChange_surjective ℚ
      (g := (characterRestrict l).toIntLinearMap) (characterRestrict_bijective_of_levi hl).surjective
    have hs₂ := ha.rationalCharacterRestrictRat_surjective hl.isConnectedReductive
    change Function.Surjective (((characterRestrict (a ≫ l)).toIntLinearMap).baseChange ℚ)
    rw [characterRestrict_comp]
    change Function.Surjective (((characterRestrict a).toIntLinearMap.comp
      (characterRestrict l).toIntLinearMap).baseChange ℚ)
    rw [LinearMap.baseChange_comp]
    exact hs₂.comp hs₁
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.baseChange_surjective ℝ hf)
    ((rationalRealTensorEquiv (characterLattice A)).symm y)
  refine ⟨rationalRealTensorEquiv (rationalCharacters P) x, ?_⟩
  have hnat := LinearMap.congr_fun (rationalRealTensorEquiv_naturality f) x
  change (rationalRealTensorEquiv (characterLattice A)) ((f.baseChange ℚ).baseChange ℝ x) =
    (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) at hnat
  change (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) = y
  rw [← hnat, hx, LinearEquiv.apply_symm_apply]

/-- Each regularity threshold is achieved by a complex character parameter. -/
private theorem exists_regularParameter (R : ℝ) :
    ∃ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam := by
  let : Module.Finite ℤ (characterLattice A) := hA.finite_characterLattice
  let : FiniteDimensional ℝ (RealTorusSpace.Vstar A) :=
    inferInstanceAs (Module.Finite ℝ (ℝ ⊗[ℤ] characterLattice A))
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  have hB : B.Nondegenerate :=
    weylInducedCharacterForm_nondegenerate hA hT r.data.f r.data.i
  let s := max R 0 + 1
  obtain ⟨v, hv⟩ := (B.toDual hB).surjective (s • r.splitComponentEvaluation)
  obtain ⟨u, hu⟩ := realParameterRestriction_surjective
    r.isCompatible.levi r.isCompatible.splitComponent v
  obtain ⟨lam, hlam⟩ := parameterRealPart_surjective u
  refine ⟨lam, ?_⟩
  rintro α ⟨hne, β, hβ, rfl⟩
  have hroot := (r.restrict_positive_eq_zero_or_mem hβ).resolve_left hne
  have hone : (1 : ℤ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    have hpos := hroot.2
    omega
  have hone' : (1 : ℝ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    exact_mod_cast hone
  have hs : 0 ≤ s := (le_max_right R 0).trans (le_add_of_nonneg_right zero_le_one)
  change R < B (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))
    ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ β))
  rw [hlam, hu, ← LinearMap.BilinForm.toDual_def hB, hv, LinearMap.smul_apply,
    r.splitComponentEvaluation_tmul, one_mul, smul_eq_mul]
  calc
    R < s := (le_max_left R 0).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone' hs

/-- The regular region is nonempty in any specified chart. -/
private theorem nonempty_regularParameter_inCoordinates (R : ℝ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    {x | r.IsRegularParameter hA hT R (e x)}.Nonempty := by
  obtain ⟨lam, hlam⟩ := r.exists_regularParameter hA hT R
  exact ⟨e.symm lam, by simpa using hlam⟩

/-! The following two lemmas are new in this module. -/

omit [LocallyOfFiniteType G.X.hom] in
/-- Regularity for a larger threshold implies regularity for a smaller one. -/
private theorem regularParameter_mono {R R' : ℝ} (hRR : R ≤ R')
    {lam : ComplexCharacterParameter F P} (h : r.IsRegularParameter hA hT R' lam) :
    r.IsRegularParameter hA hT R lam :=
  fun α hα => hRR.trans_lt (h α hα)

open Langlands.Analysis.Meromorphic in
/-- Two scalar functions meromorphic in linear coordinates that agree on the parameters of
sufficiently regular real part agree on their common holomorphy domain. -/
private theorem eqOn_of_regular {f₁ f₂ : ComplexCharacterParameter F P → ℂ}
    {S₁ S₂ : Set (ComplexCharacterParameter F P)}
    (h₁ : IsMeromorphicInCoordinatesOn f₁ S₁) (h₂ : IsMeromorphicInCoordinatesOn f₂ S₂)
    (R : ℝ) (h : ∀ lam, r.IsRegularParameter hA hT R lam → f₁ lam = f₂ lam) :
    EqOn f₁ f₂ (S₁ ∩ S₂) := by
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := h₁.1
  let e := (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  exact h₁.eqOn_of_eqOn_open h₂ e (r.isOpen_regularParameter_inCoordinates hA hT R e)
    (r.nonempty_regularParameter_inCoordinates hA hT R e) (fun s hs => h (e s) hs.1)


end Langlands.GroupScheme.ParabolicRootPresentation

/-! ## The reduction -/

namespace Langlands.Global

open Set
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- The reduction of the cocycle relation (Bernstein–Lapid, §8.6, proof of Theorem 2.3 (5)) as
a proposition: the functional equation of Eisenstein series, the meromorphic continuation of
intertwining operators, the pointwise meromorphic continuation of Eisenstein series for finite
families and the generic injectivity (8.4) together imply the cocycle relation. -/
def IntertwiningCocycleReductionStatement : Prop :=
  EisensteinFunctionalEquationStatement.{u} → IntertwiningMeromorphicContinuationStatement.{u} →
    EisensteinPointwiseContinuationStatement.{u} → EisensteinGenericInjectivityStatement.{u} →
      IntertwiningCocycleStatement.{u}

/-- **Reduction of the cocycle relation** (Bernstein–Lapid, §8.6, proof of Theorem 2.3 (5)).
The cocycle relation `M(w'w, λ) = M(w', wλ) ∘ M(w, λ)` follows from the functional equation
of Eisenstein series, the meromorphic continuation of intertwining operators, the pointwise
meromorphic continuation of Eisenstein series for finite families and the generic injectivity
(8.4) of `φ ↦ E(φ, λ)` on finite-dimensional spaces of automorphic forms. -/
theorem intertwiningCocycle_of_inputs
    (hFE : EisensteinFunctionalEquationStatement.{u})
    (hIC : IntertwiningMeromorphicContinuationStatement.{u})
    (hPC : EisensteinPointwiseContinuationStatement.{u})
    (hGI : EisensteinGenericInjectivityStatement.{u}) :
    IntertwiningCocycleStatement.{u} := by
  intro F _ _ G P M U Q M' V Q'' M'' V'' A A' _ _ _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT
    q _ iV l' _ a' r' _ _ _ hA' hT' π' q'' _ iV'' l'' _ π'' w w' c c'
    hG hU hV hQ'' hV'' hl'' hmul'' hπ' hπ'' hw hw' K hK hK' hK'' N d rho hsmooth hcalc φ
    hKmax hrho hφ k ψ coeff D hψ hcoeff hMw k' χ coeff' D' hcoeff' hMw' k'' χ'' coeff'' D''
    hcoeff'' hMww lam₀ hlam₀ hWlam₀ g₀
  classical
  have hcI : IsIso c := hw.isIso
  have hc'I : IsIso c' := hw'.isIso
  have hl : IsRationalLeviSubgroup l := r.isCompatible.levi
  have hl' : IsRationalLeviSubgroup l' := r'.isCompatible.levi
  -- Weyl parameters as linear equivalences, and their composition.
  obtain ⟨We, hWe⟩ := exists_weylParameter_linearEquiv l l' hl hl' c π' hπ'
  obtain ⟨We'', hWe''⟩ := exists_weylParameter_linearEquiv l l'' hl hl'' (c' ≫ c) π'' hπ''
  have hWapp : ∀ x, We x = weylParameter l c π' x := fun x => LinearMap.congr_fun hWe x
  have hW''app : ∀ x, We'' x = weylParameter l (c' ≫ c) π'' x :=
    fun x => LinearMap.congr_fun hWe'' x
  have hcomp : ∀ x, weylParameter l' c' π'' (weylParameter l c π' x) =
      weylParameter l (c' ≫ c) π'' x := by
    have hid : ∀ y, characterRestrict l' (characterRestrict π' y) = y :=
      characterRestrict_rightInverse l' π' hπ'
    have hL : (weylParameter l' c' π'').comp (weylParameter l c π') =
        weylParameter l (c' ≫ c) π'' := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s χ₀
      change weylParameter l' c' π'' (weylParameter l c π' (s ⊗ₜ[ℤ] χ₀)) =
        weylParameter l (c' ≫ c) π'' (s ⊗ₜ[ℤ] χ₀)
      rw [weylParameter_tmul, weylParameter_tmul, weylParameter_tmul]
      congr 1
      simp only [characterRestrict_comp, AddMonoidHom.comp_apply, hid]
    exact fun x => LinearMap.congr_fun hL x
  -- The composite Weyl element.
  have hw'' : IsWeylConjugation p l q'' l'' (w' * w) (c' ≫ c) := by
    refine ⟨inferInstance, ?_⟩
    have hinv : (G.innerIso (w' * w)).inv = (G.innerIso w').inv ≫ (G.innerIso w).inv := by
      have h : G.innerIso (w' * w) = G.innerIso w ≪≫ G.innerIso w' :=
        Iso.ext (innerIso_mul_hom G w' w)
      rw [h, Iso.trans_inv]
    calc (c' ≫ c) ≫ l ≫ p = c' ≫ (c ≫ l ≫ p) := Category.assoc _ _ _
      _ = c' ≫ (l' ≫ q ≫ (G.innerIso w).inv) := by rw [hw.comp_eq]
      _ = (c' ≫ l' ≫ q) ≫ (G.innerIso w).inv := by simp only [Category.assoc]
      _ = (l'' ≫ q'' ≫ (G.innerIso w').inv) ≫ (G.innerIso w).inv := by rw [hw'.comp_eq]
      _ = l'' ≫ q'' ≫ (G.innerIso (w' * w)).inv := by simp only [Category.assoc, hinv]
  -- A root presentation of `Q''` with split component `A'`.
  obtain ⟨a'', ha''⟩ : ∃ a'' : A'.toGrp ⟶ M'', IsSplitComponent a'' :=
    ⟨_, r'.isCompatible.splitComponent.comp_iso (asIso c').symm⟩
  obtain ⟨r''⟩ := parabolicRootPresentationExistence F G hG Q'' M'' A' q'' l'' a'' hQ'' hl'' ha''
  have : Mono r''.data.i.hom.hom.left := r''.isCompatible.maximalSplit.isSplitSubtorus.mono
  have : Fintype (relativeWeylGroup r''.data.i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup r''.data.i r''.isCompatible.maximalSplit)
  have : Mono (CommGroupScheme.groupHom r''.data.f).hom.hom.left := by
    have := r''.isCompatible.splitComponent.1.isSplitSubtorus.mono
    have := r''.isCompatible.levi.isClosedSubgroup.mono
    have := r''.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a'' ≫ l'' ≫ q'').hom.hom.left := by
      change Mono (a''.hom.hom.left ≫ l''.hom.hom.left ≫ q''.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r''.isCompatible.factor_comp)
  have hT'' : IsSplitTorus r''.data.T.toGrp := r''.isCompatible.maximalSplit.isSplitSubtorus.1
  -- Continued Eisenstein series of `φ` and of the `ψ i`.
  obtain ⟨EP, DP, hEP, RP, hRP⟩ := hPC F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth
    hcalc hKmax hrho Unit (fun _ => φ) (fun _ => hφ)
  have hFD : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hEP () 1).1
  have hDP : OpenDenseInCoordinates DP := (hEP () 1).openDense
  obtain ⟨EQ, DQ, hEQ, RQ, hRQ⟩ := hPC F G Q M' V A' q iV l' a' r' hA' hT' hG hV K hK' rho
    hsmooth hcalc hKmax hrho (Fin k) ψ hψ
  -- Continuation of the intertwining operators into `Q''`.
  obtain ⟨k₁, ψ₁, c₁, D₁, hψ₁, hc₁, R₁, hR₁⟩ := hIC F G P M U Q'' M'' V'' A p iU l a r hA hT
    q'' iV'' l'' π'' (w' * w) (c' ≫ c) hG hU hQ'' hV'' hl'' hmul'' hπ'' hw'' K hK hK'' rho
    hsmooth hcalc φ hKmax hrho hφ
  choose k₂ ψ₂ c₂ D₂ hψ₂ hc₂ hR₂ using fun i : Fin k => hIC F G Q M' V Q'' M'' V'' A' q iV l'
    a' r' hA' hT' q'' iV'' l'' π'' w' c' hG hV hQ'' hV'' hl'' hmul'' hπ'' hw' K hK' hK'' rho
    hsmooth hcalc (ψ i) hKmax hrho (hψ i)
  -- Continued Eisenstein series of all forms on `Q''`.
  let ψ'' : (Fin k₁ ⊕ Σ i, Fin (k₂ i)) → AdelicGroupPoints F G → ℂ :=
    Sum.elim ψ₁ (fun x => ψ₂ x.1 x.2)
  have hψ'' : ∀ x, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F q'' iV'' l'') (K.comap (ofInfinite F G).toMonoidHom) rho
      (ψ'' x) := by
    rintro (b | ⟨i, b⟩)
    exacts [hψ₁ b, hψ₂ i b]
  obtain ⟨E'', DC, hE'', RC, hRC⟩ := hPC F G Q'' M'' V'' A' q'' iV'' l'' a'' r'' hA' hT'' hG
    hV'' K hK'' rho hsmooth hcalc hKmax hrho _ ψ'' hψ''
  -- Common domains, with empty families allowed.
  obtain ⟨hc₁t, hD₁t⟩ := isMeromorphicInCoordinatesOn_iInter_const hc₁
  obtain ⟨hcoefft, hDt⟩ := isMeromorphicInCoordinatesOn_iInter_const hcoeff
  obtain ⟨hEQt, hDQt⟩ := isMeromorphicInCoordinatesOn_iInter_const
    (h := fun x : Fin k × AdelicGroupPoints F G => fun mu => EQ x.1 mu x.2)
    (fun x => hEQ x.1 x.2)
  have hD₂t := fun i : Fin k => isMeromorphicInCoordinatesOn_iInter_const (hc₂ i)
  obtain ⟨hE''t, hDCt⟩ := isMeromorphicInCoordinatesOn_iInter_const
    (h := fun x : (Fin k₁ ⊕ Σ i, Fin (k₂ i)) × AdelicGroupPoints F G => fun mu => E'' x.1 mu x.2)
    (fun x => hE'' x.1 x.2)
  set DQt := ⋂ _ : Fin k × AdelicGroupPoints F G, DQ
  set DCt := ⋂ _ : (Fin k₁ ⊕ Σ i, Fin (k₂ i)) × AdelicGroupPoints F G, DC
  -- The three functional equations.
  have hFE1 := hFE F G P M U Q'' M'' V'' A A' p iU l a r hA hT q'' iV'' l'' a'' r'' hA' hT''
    π'' (w' * w) (c' ≫ c) hG hU hV'' hπ'' hw'' K hK hK'' rho hsmooth hcalc φ hKmax hrho hφ
    (EP ()) DP (fun g => hEP () g) ⟨RP, fun lam h => hRP lam h ()⟩
    k₁ ψ₁ c₁ _ hψ₁ hc₁t ⟨R₁, hR₁⟩
    (fun b => E'' (Sum.inl b)) DCt (fun b g => hE''t (Sum.inl b, g))
    (fun b => ⟨RC, fun mu h => hRC mu h (Sum.inl b)⟩)
  have hFE2 := hFE F G P M U Q M' V A A' p iU l a r hA hT q iV l' a' r' hA' hT' π' w c
    hG hU hV hπ' hw K hK hK' rho hsmooth hcalc φ hKmax hrho hφ
    (EP ()) DP (fun g => hEP () g) ⟨RP, fun lam h => hRP lam h ()⟩
    k ψ coeff _ hψ hcoefft hMw
    EQ DQt (fun i g => hEQt (i, g)) (fun i => ⟨RQ, fun mu h => hRQ mu h i⟩)
  have hFE3 := fun i : Fin k => hFE F G Q M' V Q'' M'' V'' A' A' q iV l' a' r' hA' hT'
    q'' iV'' l'' a'' r'' hA' hT'' π'' w' c' hG hV hV'' hπ'' hw' K hK' hK'' rho hsmooth hcalc
    (ψ i) hKmax hrho (hψ i)
    (EQ i) DQt (fun g => hEQt (i, g)) ⟨RQ, fun mu h => hRQ mu h i⟩
    (k₂ i) (ψ₂ i) (c₂ i) _ (hψ₂ i) (hD₂t i).1 (hR₂ i)
    (fun b => E'' (Sum.inr ⟨i, b⟩)) DCt (fun b g => hE''t (Sum.inr ⟨i, b⟩, g))
    (fun b => ⟨RC, fun mu h => hRC mu h (Sum.inr ⟨i, b⟩)⟩)
  -- The generic set of parameters.
  set Θ := DP ∩ (⋂ _ : Fin k₁, D₁) ∩ (⋂ _ : Fin k, D) ∩
    We ⁻¹' (DQt ∩ ⋂ i, ⋂ _ : Fin (k₂ i), D₂ i) ∩ We'' ⁻¹' DCt with hΘdef
  have hΘ : OpenDenseInCoordinates Θ :=
    (((hDP.inter hD₁t).inter hDt).inter
      ((hDQt.inter (OpenDenseInCoordinates.iInter fun i => (hD₂t i).2)).preimage We)).inter
      (hDCt.preimage We'')
  -- Relation in `𝒜_{Q''}` from injectivity at a generic parameter.
  have hstar0 : ∀ lam ∈ Θ,
      (∀ C : (Fin k₁ ⊕ Σ i, Fin (k₂ i)) → ℂ,
        (∀ g, ∑ x, C x * E'' x (We'' lam) g = 0) → ∀ g, ∑ x, C x * ψ'' x g = 0) →
      ∀ g, ∑ b, c₁ b lam * ψ₁ b g =
        ∑ i, coeff i lam * ∑ b, c₂ i b (weylParameter l c π' lam) * ψ₂ i b g := by
    intro lam hlam hinj g
    obtain ⟨⟨⟨⟨hP, h1⟩, ht⟩, hQ2⟩, hC⟩ := hlam
    have hQ2' : weylParameter l c π' lam ∈ DQt ∩ ⋂ i, ⋂ _ : Fin (k₂ i), D₂ i := by
      rw [← hWapp]; exact hQ2
    have hC' : weylParameter l (c' ≫ c) π'' lam ∈ DCt := by
      rw [← hW''app]; exact hC
    have h1' : ∀ g, EP () lam g =
        ∑ b, c₁ b lam * E'' (Sum.inl b) (weylParameter l (c' ≫ c) π'' lam) g :=
      hFE1 lam ⟨hP, h1⟩ hC'
    have h2' : ∀ g, EP () lam g = ∑ i, coeff i lam * EQ i (weylParameter l c π' lam) g :=
      hFE2 lam ⟨hP, ht⟩ hQ2'.1
    have h3' : ∀ i g, EQ i (weylParameter l c π' lam) g =
        ∑ b, c₂ i b (weylParameter l c π' lam) *
          E'' (Sum.inr ⟨i, b⟩) (weylParameter l (c' ≫ c) π'' lam) g := by
      intro i g
      rw [← hcomp lam]
      exact hFE3 i (weylParameter l c π' lam) ⟨hQ2'.1, mem_iInter.mp hQ2'.2 i⟩
        (by rw [hcomp]; exact hC') g
    let C : (Fin k₁ ⊕ Σ i, Fin (k₂ i)) → ℂ := Sum.elim (fun b => c₁ b lam)
      (fun x => -(coeff x.1 lam * c₂ x.1 x.2 (weylParameter l c π' lam)))
    have hrel : ∀ g, ∑ x, C x * E'' x (We'' lam) g = 0 := by
      intro g
      rw [hW''app, Fintype.sum_sum_type, Fintype.sum_sigma]
      have e1 : ∑ b, C (Sum.inl b) * E'' (Sum.inl b) (weylParameter l (c' ≫ c) π'' lam) g =
          EP () lam g := (h1' g).symm
      have e2 : ∑ i, ∑ b, C (Sum.inr ⟨i, b⟩) *
          E'' (Sum.inr ⟨i, b⟩) (weylParameter l (c' ≫ c) π'' lam) g = -EP () lam g := by
        rw [h2' g, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h3' i g, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [C, Sum.elim_inr]
        ring
      rw [e1, e2, add_neg_cancel]
    have hrelψ := hinj C hrel g
    rw [Fintype.sum_sum_type, Fintype.sum_sigma] at hrelψ
    have e3 : ∑ i, ∑ b, C (Sum.inr ⟨i, b⟩) * ψ'' (Sum.inr ⟨i, b⟩) g =
        -∑ i, coeff i lam * ∑ b, c₂ i b (weylParameter l c π' lam) * ψ₂ i b g := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [C, ψ'', Sum.elim_inr]
      ring
    rw [e3] at hrelψ
    exact add_neg_eq_zero.mp hrelψ
  -- A chart of `X^*(P) ⊗ ℂ` and the open dense injectivity set in it.
  let e := (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  obtain ⟨O, hO, hOd, hOinj⟩ := hGI F G Q'' M'' V'' A' q'' iV'' l'' a'' r'' hA' hT'' hG hV''
    K hK'' rho hsmooth hcalc hKmax hrho _ ψ'' hψ'' E'' DCt (fun x g => hE''t (x, g))
    (fun x => ⟨RC, fun mu h => hRC mu h x⟩) _ (e.trans We'')
  have hstar : ∀ s ∈ O, e s ∈ Θ → ∀ g, ∑ b, c₁ b (e s) * ψ₁ b g =
      ∑ i, coeff i (e s) * ∑ b, c₂ i b (weylParameter l c π' (e s)) * ψ₂ i b g :=
    fun s hs hsΘ => hstar0 (e s) hsΘ (hOinj s hs hsΘ.2)
  -- Transfer from the given expansions to the automorphic ones.
  obtain ⟨R'', hR''⟩ := hMww
  choose R' hR' using hMw'
  have hT1 : EqOn (fun lam => ∑ j, coeff'' j lam * χ'' j g₀)
      (fun lam => ∑ b, c₁ b lam * ψ₁ b g₀) ((⋂ _ : Fin k'', D'') ∩ ⋂ _ : Fin k₁, D₁) :=
    r.eqOn_of_regular hA hT
      (IsMeromorphicInCoordinatesOn.sum_iInter fun j => (hcoeff'' j).mul_const (χ'' j g₀))
      (IsMeromorphicInCoordinatesOn.sum_iInter fun b => (hc₁ b).mul_const (ψ₁ b g₀))
      (max R'' R₁) fun lam hreg =>
        (hR'' lam (r.regularParameter_mono hA hT (le_max_left _ _) hreg) g₀).symm.trans
          (hR₁ lam (r.regularParameter_mono hA hT (le_max_right _ _) hreg) g₀)
  have hFDQ : FiniteDimensional ℂ (ComplexCharacterParameter F Q) :=
    FiniteDimensional.of_injective We.symm.toLinearMap We.symm.injective
  have hf₂ : ∀ i, IsMeromorphicInCoordinatesOn (fun mu => ∑ j, coeff' i j mu * χ j g₀)
      (⋂ _ : Fin k', D') := fun i =>
    IsMeromorphicInCoordinatesOn.sum_iInter fun j => (hcoeff' i j).mul_const (χ j g₀)
  have hT2 : ∀ i, EqOn (fun mu => ∑ j, coeff' i j mu * χ j g₀)
      (fun mu => ∑ b, c₂ i b mu * ψ₂ i b g₀) ((⋂ _ : Fin k', D') ∩ ⋂ _ : Fin (k₂ i), D₂ i) := by
    intro i
    obtain ⟨R₂, hR₂'⟩ := hR₂ i
    exact r'.eqOn_of_regular hA' hT' (hf₂ i)
      (IsMeromorphicInCoordinatesOn.sum_iInter fun b => (hc₂ i b).mul_const (ψ₂ i b g₀))
      (max (R' i) R₂) fun mu hreg =>
        (hR' i mu (r'.regularParameter_mono hA' hT' (le_max_left _ _) hreg) g₀).symm.trans
          (hR₂' mu (r'.regularParameter_mono hA' hT' (le_max_right _ _) hreg) g₀)
  -- The two sides as meromorphic functions of `λ`.
  have hF1 : IsMeromorphicInCoordinatesOn (fun lam => ∑ j, coeff'' j lam * χ'' j g₀)
      (⋂ _ : Fin k'', D'') :=
    IsMeromorphicInCoordinatesOn.sum_iInter fun j => (hcoeff'' j).mul_const (χ'' j g₀)
  have hF2 : IsMeromorphicInCoordinatesOn
      (fun lam => ∑ i, coeff i lam * ∑ j, coeff' i j (weylParameter l c π' lam) * χ j g₀)
      (⋂ _ : Fin k, (D ∩ We ⁻¹' ⋂ _ : Fin k', D')) := by
    refine IsMeromorphicInCoordinatesOn.sum_iInter fun i => ?_
    have h := (hcoeff i).mul ((hf₂ i).comp_linearEquiv We)
    convert h using 1
    funext lam
    simp only [Pi.mul_apply, Function.comp_apply, hWapp]
  -- Agreement on a nonempty open set of one chart, then everywhere.
  have hO' : IsOpen (O ∩ e ⁻¹' Θ) := hO.inter (hΘ _ e).1
  have hO'ne : (O ∩ e ⁻¹' Θ).Nonempty :=
    (hOd.inter_of_isOpen_left (hΘ _ e).2 hO).nonempty
  have heq := hF1.eqOn_of_eqOn_open hF2 e hO' hO'ne (by
    rintro s ⟨⟨hsO, hsΘ⟩, hs₁, hs₂⟩
    have hs₂' := mem_iInter.mp hs₂
    change ∑ j, coeff'' j (e s) * χ'' j g₀ =
      ∑ i, coeff i (e s) * ∑ j, coeff' i j (weylParameter l c π' (e s)) * χ j g₀
    refine (hT1 ⟨hs₁, hsΘ.1.1.1.2⟩).trans ((hstar s hsO hsΘ g₀).trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hW₁ : weylParameter l c π' (e s) ∈ ⋂ _ : Fin k', D' := by
      rw [← hWapp]; exact (hs₂' i).2
    have hW₂ : weylParameter l c π' (e s) ∈ ⋂ _ : Fin (k₂ i), D₂ i := by
      rw [← hWapp]; exact mem_iInter.mp hsΘ.1.2.2 i
    exact (hT2 i ⟨hW₁, hW₂⟩).symm)
  refine heq ⟨mem_iInter.mpr fun _ => hlam₀.2, mem_iInter.mpr fun _ => ⟨hlam₀.1, ?_⟩⟩
  rw [mem_preimage, hWapp]
  exact mem_iInter.mpr fun _ => hWlam₀

/-- The reduction of the cocycle relation, in the form of
`IntertwiningCocycleReductionStatement`. -/
theorem intertwiningCocycleReduction : IntertwiningCocycleReductionStatement.{u} :=
  fun hFE hIC hPC hGI => intertwiningCocycle_of_inputs hFE hIC hPC hGI

end Langlands.Global
