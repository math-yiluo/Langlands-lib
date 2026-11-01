import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Scalarization through normed product coordinates -/

noncomputable section
universe u v w z
open scoped Topology
open Topology
set_option autoImplicit false

namespace Langlands.Analysis

/-- A continuous linear map from an arbitrary product of real normed spaces
into a normed space uses only finitely many coordinates. -/
theorem continuousLinearMap_product_factors
    {ι : Type u} {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (∀ i, F i) →L[ℝ] G) :
    ∃ (s : Finset ι) (M : (∀ i : s, F i.val) →L[ℝ] G),
      ∀ x, L x = M (fun i => x i.val) := by
  classical
  let p := SeminormFamily.sigma
    (fun i : ι => fun _ : Fin 1 => (normSeminorm ℝ (F i)).comp (LinearMap.proj i))
  have hp : WithSeminorms p :=
    withSeminorms_pi (fun i => norm_withSeminorms ℝ (F i))
  obtain ⟨t, C, _, hC⟩ := Seminorm.bound_of_continuous hp
    ((normSeminorm ℝ G).comp L.toLinearMap) L.continuous.norm
  let s : Finset ι := t.image Sigma.fst
  let J : (∀ i : s, F i.val) →L[ℝ] (∀ i, F i) :=
    ContinuousLinearMap.pi (fun i =>
      if h : i ∈ s then
        (ContinuousLinearMap.proj (⟨i, h⟩ : s) :
          (∀ j : s, F j.val) →L[ℝ] F i)
      else 0)
  refine ⟨s, L.comp J, ?_⟩
  intro x
  have hzero : L (x - J (fun i : s => x i.val)) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht : (t.sup p) (x - J (fun i : s => x i.val)) = 0 := by
      apply le_antisymm _ (apply_nonneg _ _)
      rw [Seminorm.finset_sup_apply]
      norm_cast
      apply Finset.sup_le
      intro j hj
      have hs : j.1 ∈ s := Finset.mem_image.mpr ⟨j, hj, rfl⟩
      change (p j) (x - J (fun i : s => x i.val)) ≤ 0
      simp [p, SeminormFamily.sigma, Seminorm.comp_apply, J, hs]
    have h := hC (x - J (fun i : s => x i.val))
    simpa [ht] using h
  simpa only [map_sub, sub_eq_zero, ContinuousLinearMap.comp_apply] using hzero

/-- Coordinatewise smooth parameter families remain smooth after any continuous
linear map from their product to a normed space. The infinite product itself
need not carry a norm. -/
theorem contDiffOn_comp_product_of_coordinates
    {ι : Type u} {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {E : Type z} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (∀ i, F i) →L[ℝ] G) {f : E → ∀ i, F i}
    {s : Set E} {m : WithTop ℕ∞}
    (hf : ∀ i, ContDiffOn ℝ m (fun x => f x i) s) :
    ContDiffOn ℝ m (fun x => L (f x)) s := by
  obtain ⟨t, M, hM⟩ := continuousLinearMap_product_factors L
  have h : ContDiffOn ℝ m (fun x => M (fun i : t => f x i.val)) s :=
    M.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => hf i.val)
  simpa only [← hM] using h

/-- A continuous linear map with finite-dimensional target extends across a
linear topological embedding into a product of normed spaces. -/
theorem continuousLinearMap_extends_product_embedding
    {ι : Type u} {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V : Type z} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (e : V →L[ℝ] ∀ i, F i) (he : IsEmbedding e) (L : V →L[ℝ] G) :
    ∃ M : (∀ i, F i) →L[ℝ] G, ∀ x, M (e x) = L x := by
  let er : V ≃ₗ[ℝ] e.range := LinearEquiv.ofInjective e.toLinearMap he.injective
  have her : ∀ y : e.range, e (er.symm y) = y.val := by
    intro y
    exact congrArg Subtype.val (er.apply_symm_apply y)
  have hcont : Continuous er.symm := he.isInducing.continuous_iff.mpr (by
    simpa only [Function.comp_def, her] using
      (continuous_subtype_val : Continuous (fun y : e.range => y.val)))
  let Lr : e.range →L[ℝ] G :=
    ⟨L.toLinearMap.comp er.symm.toLinearMap, L.continuous.comp hcont⟩
  obtain ⟨M, hM⟩ := Lr.exist_extension_of_finiteDimensional_range
  refine ⟨M, fun x => ?_⟩
  have hh := congrArg (fun Q : e.range →L[ℝ] G => Q (er x)) hM
  simpa [Lr, er] using hh.symm

/-- Smoothness can be tested in normed coordinates before applying a continuous
linear functional with finite-dimensional range. -/
theorem contDiffOn_scalar_of_product_embedding
    {ι : Type u} {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V : Type z} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : V →L[ℝ] ∀ i, F i) (he : IsEmbedding e) (L : V →L[ℝ] G)
    {f : E → V} {s : Set E} {m : WithTop ℕ∞}
    (hf : ∀ i, ContDiffOn ℝ m (fun x => e (f x) i) s) :
    ContDiffOn ℝ m (fun x => L (f x)) s := by
  obtain ⟨M, hM⟩ := continuousLinearMap_extends_product_embedding e he L
  simpa only [hM] using contDiffOn_comp_product_of_coordinates M hf

/-- A scalar derivative can be identified in the normed coordinates without
putting a norm or a differential calculus on the embedded source space. -/
theorem fderiv_scalar_of_product_embedding_apply
    {ι : Type u} {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V : Type z} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : V →L[ℝ] ∀ i, F i) (he : IsEmbedding e) (L : V →L[ℝ] G)
    {f : E → V} {x d : E} {v : V}
    (hf : ∀ i, DifferentiableAt ℝ (fun y => e (f y) i) x)
    (hv : ∀ i, fderiv ℝ (fun y => e (f y) i) x d = e v i) :
    fderiv ℝ (fun y => L (f y)) x d = L v := by
  obtain ⟨M, hM⟩ := continuousLinearMap_extends_product_embedding e he L
  obtain ⟨t, N, hN⟩ := continuousLinearMap_product_factors M
  let D : E →L[ℝ] (∀ i : t, F i.val) :=
    ContinuousLinearMap.pi fun i => fderiv ℝ (fun y => e (f y) i.val) x
  have hD : HasFDerivAt (fun y => fun i : t => e (f y) i.val) D x :=
    hasFDerivAt_pi.mpr fun i => (hf i.val).hasFDerivAt
  have hscalar : HasFDerivAt (fun y => L (f y)) (N.comp D) x := by
    have hh := N.hasFDerivAt.comp x hD
    convert hh using 1
    funext y
    exact (hM (f y)).symm.trans (hN (e (f y)))
  rw [hscalar.fderiv]
  change N (D d) = L v
  have hDd : D d = fun i : t => e v i.val := by
    funext i
    exact hv i.val
  rw [hDd, ← hN, hM]

end Langlands.Analysis
