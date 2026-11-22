import Langlands.Analysis.Meromorphic.ScalarIdentity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Scalar meromorphy on an open cover -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set
open scoped Manifold

section Evaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {U : Set M}

/-- Continuous linear scalar evaluation preserves weak meromorphy. -/
theorem IsMeromorphicOn.comp_continuousLinearMap {f : M → V}
    (hf : IsMeromorphicOn I f U) (μ : V →L[ℂ] ℂ) :
    IsMeromorphicOn I (μ ∘ f) U := by
  refine ⟨hf.1, hf.2.1, fun ν => hf.2.2.1 (ν.comp μ), fun x => ?_⟩
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  refine ⟨W, hW, hcW, hxW, d, μ ∘ n, hd, hdnz, fun ν => hn (ν.comp μ), ?_⟩
  intro y hy
  change d y • μ (f y) = μ (n y)
  rw [← map_smul, hdf y hy]

/-- Changing a function away from its holomorphy domain preserves its local
holomorphic denominator presentations. -/
theorem IsMeromorphicOn.congr_domain {f g : M → V}
    (hf : IsMeromorphicOn I f U) (h : EqOn g f U) : IsMeromorphicOn I g U := by
  refine ⟨hf.1, hf.2.1, fun μ => (hf.2.2.1 μ).congr (fun x hx => congrArg μ (h hx)),
    fun x => ?_⟩
  obtain ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, hdf⟩ := hf.2.2.2 x
  exact ⟨W, hW, hcW, hxW, d, n, hd, hdnz, hn, fun y hy => (h hy.1).symm ▸ hdf y hy⟩

end Evaluation

section Cover

variable {E : Type*} [NormedAddCommGroup E] {O : TopologicalSpace.Opens E} {S : Set O}

private theorem mem_openChart_source (o x : O) : x ∈ (chartAt E o).source := by
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  trivial

private theorem openChart_symm_apply_coe (o x : O) : (chartAt E o).symm x.val = x :=
  (chartAt E o).left_inv (mem_openChart_source o x)

variable [NormedSpace ℂ E]

private theorem differentiableOn_in_openChart (o : O) {a : O → ℂ}
    (ha : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) a S) :
    DifferentiableOn ℂ (a ∘ (chartAt E o).symm) (Subtype.val '' S) := by
  have htarget : Subtype.val '' S ⊆ (chartAt E o).target := by
    rintro _ ⟨x, _, rfl⟩
    exact (chartAt E o).map_source (mem_openChart_source o x)
  have hmaps : MapsTo (chartAt E o).symm (Subtype.val '' S) S := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [openChart_symm_apply_coe]
  exact (ha.comp ((mdifferentiableOn_atlas_symm (I := 𝓘(ℂ, E))
    (chart_mem_atlas E o)).mono htarget) hmaps).differentiableOn

/-- A function meromorphic on each piece of an open cover is meromorphic
on the whole space, with holomorphy domain the union of the local domains. -/
theorem isMeromorphicOn_of_openCover {ι : Type*} {f : E → ℂ}
    (O : ι → TopologicalSpace.Opens E) (D : ∀ i, Set (O i))
    (hcover : ∀ x : E, ∃ i, x ∈ O i)
    (hf : ∀ i, IsMeromorphicOn 𝓘(ℂ, E) (f ∘ Subtype.val) (D i)) :
    IsMeromorphicOn 𝓘(ℂ, E) f (⋃ i, Subtype.val '' D i) := by
  let U := ⋃ i, Subtype.val '' D i
  have hO (i : ι) := (O i).2.isOpenEmbedding_subtypeVal
  have hU : IsOpen U := isOpen_iUnion fun i => (hO i).isOpenMap _ (hf i).1
  have hUmem (i : ι) : Subtype.val '' D i ⊆ U :=
    subset_iUnion (fun j => (Subtype.val : O j → E) '' D j) i
  have hdU : Dense U := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact closure_mono (hUmem i) (map_mem_closure continuous_subtype_val ((hf i).2.1 ⟨x, hi⟩)
      (mapsTo_image _ _))
  have hdf : DifferentiableOn ℂ f U := by
    intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
    have hd := differentiableOn_in_openChart z ((hf i).2.2.1 (ContinuousLinearMap.id ℂ ℂ))
    have heq : EqOn f ((fun t : O i => (ContinuousLinearMap.id ℂ ℂ) (f t.val)) ∘
        (chartAt E z).symm) (Subtype.val '' D i) := by
      rintro _ ⟨y, _, rfl⟩
      change f y.val = f ((chartAt E z).symm y.val).val
      rw [openChart_symm_apply_coe]
    have hd' := hd.congr heq
    have hopen := (hO i).isOpenMap _ (hf i).1
    have hz' : z.val ∈ Subtype.val '' D i := mem_image_of_mem _ hz
    exact ((hd' z.val hz').differentiableAt (hopen.mem_nhds hz')).differentiableWithinAt
  refine ⟨hU, hdU, isHolomorphicOn_iff_differentiableOn_scalar.mpr hdf, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hcover x
  let o : O i := ⟨x, hi⟩
  obtain ⟨S, hS, hcS, hoS, d, n, hd, hdnz, hn, hlocal⟩ := (hf i).2.2.2 o
  let W := Subtype.val '' S
  let V := Subtype.val '' (D i ∩ S)
  let j := (chartAt E o).symm
  have hd' : DifferentiableOn ℂ (d ∘ j) W := differentiableOn_in_openChart o hd
  have hn' : DifferentiableOn ℂ (n ∘ j) W :=
    differentiableOn_in_openChart o (hn (ContinuousLinearMap.id ℂ ℂ))
  have hVW : V ⊆ W := image_mono inter_subset_right
  have hVU : V ⊆ U := (image_mono inter_subset_left).trans (hUmem i)
  have hclosure : W ⊆ closure V := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ closure (D i ∩ S) := by
      simpa only [inter_comm] using (hf i).2.1.open_subset_closure_inter hS hy
    exact map_mem_closure continuous_subtype_val hy' (mapsTo_image _ _)
  have heq : EqOn ((d ∘ j) * f) (n ∘ j) V := by
    rintro _ ⟨y, hy, rfl⟩
    change d (j y.val) * f y.val = n (j y.val)
    simp only [j, openChart_symm_apply_coe]
    exact hlocal y hy
  have heq' := heq.of_subset_closure
    ((hd'.continuousOn.mono inter_subset_right).mul (hdf.continuousOn.mono inter_subset_left))
    (hn'.continuousOn.mono inter_subset_right) (subset_inter hVU hVW)
    (inter_subset_right.trans hclosure)
  refine ⟨W, (hO i).isOpenMap _ hS, hcS.image _ continuous_subtype_val.continuousOn,
    ⟨o, hoS, rfl⟩, d ∘ j, n ∘ j, hd'.mdifferentiableOn, ?_,
    isHolomorphicOn_iff_differentiableOn_scalar.mpr hn', fun y hy => heq' hy⟩
  obtain ⟨y, hy, hny⟩ := hdnz
  exact ⟨y.val, mem_image_of_mem _ hy, by simpa only [Function.comp_apply, j,
    openChart_symm_apply_coe] using hny⟩

end Cover

end Langlands.Analysis.Meromorphic
