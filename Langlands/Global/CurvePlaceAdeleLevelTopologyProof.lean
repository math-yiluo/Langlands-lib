import Langlands.Global.CurvePlaceAdeleLevelTopologyStatement

/-! # Proof of the topology of actual discrete curve-place adelic levels -/

noncomputable section

universe u

open IsDedekindDomain Topology
open scoped RestrictedProduct

namespace Langlands.Global

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

theorem continuous_curvePlaceAdeleLevelProductEquiv (S : Finset (AlgebraicCurve.Place k F)) :
    Continuous (curvePlaceAdeleLevelProductEquiv k F S) := by
  change Continuous (fun a : curvePlaceAdeleLevel k F S =>
    ((fun v : {v : AlgebraicCurve.Place k F // v ∈ S} =>
      (a : CurvePlaceAdeleRing k F) v.1),
      fun v : {v : AlgebraicCurve.Place k F // v ∉ S} =>
        (⟨(a : CurvePlaceAdeleRing k F) v.1, a.property v.1 v.property⟩ :
          curvePlaceCompletionIntegers v.1)))
  apply Continuous.prodMk
  · exact continuous_pi (fun v =>
      (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val)
  · apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val

theorem continuous_curvePlaceAdeleLevelAssemble (S : Finset (AlgebraicCurve.Place k F)) :
    Continuous (curvePlaceAdeleLevelAssemble k F S) := by
  classical
  let P := (∀ v : {v : AlgebraicCurve.Place k F // v ∈ S}, curvePlaceCompletion v.1) ×
    (∀ v : {v : AlgebraicCurve.Place k F // v ∉ S}, curvePlaceCompletionIntegers v.1)
  let g : P → Πʳ v : AlgebraicCurve.Place k F,
      [curvePlaceCompletion v, curvePlaceCompletionIntegers v]_[
        Filter.principal (S : Set (AlgebraicCurve.Place k F))ᶜ] :=
    fun p => ⟨fun v => (curvePlaceAdeleLevelAssemble k F S p : CurvePlaceAdeleRing k F) v,
      Filter.eventually_principal.mpr (fun v hv =>
        (curvePlaceAdeleLevelAssemble k F S p).property v hv)⟩
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    by_cases hv : v ∈ S
    · change Continuous (fun p : P =>
        (if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩).val :
          curvePlaceCompletion v))
      simpa only [dite_eq_left hv, Function.comp_def] using
        (continuous_apply (⟨v, hv⟩ : {v : AlgebraicCurve.Place k F // v ∈ S})).comp
          (show Continuous (fun p : P => p.1) from continuous_fst)
    · change Continuous (fun p : P =>
        (if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩).val :
          curvePlaceCompletion v))
      simpa only [dite_eq_right hv, Function.comp_def] using continuous_subtype_val.comp
        ((continuous_apply (⟨v, hv⟩ : {v : AlgebraicCurve.Place k F // v ∉ S})).comp
          (show Continuous (fun p : P => p.2) from continuous_snd))
  have hS : Filter.cofinite ≤ Filter.principal (S : Set (AlgebraicCurve.Place k F))ᶜ := by simp
  have h : Continuous (fun p : P =>
      (curvePlaceAdeleLevelAssemble k F S p : CurvePlaceAdeleRing k F)) :=
    (RestrictedProduct.continuous_inclusion hS).comp hg
  exact h.subtype_mk _

theorem curvePlaceAdeleLevelProductEquiv_isHomeomorph (S : Finset (AlgebraicCurve.Place k F)) :
    IsHomeomorph (curvePlaceAdeleLevelProductEquiv k F S) :=
  (show curvePlaceAdeleLevel k F S ≃ₜ _ from
    { toEquiv := (curvePlaceAdeleLevelProductEquiv k F S).toEquiv
      continuous_toFun := continuous_curvePlaceAdeleLevelProductEquiv k F S
      continuous_invFun := continuous_curvePlaceAdeleLevelAssemble k F S }).isHomeomorph

theorem curvePlaceAdeleLevelMap_isOpenEmbedding {S T : Finset (AlgebraicCurve.Place k F)}
    (hST : S ⊆ T) : IsOpenEmbedding (curvePlaceAdeleLevelMap k F hST) := by
  exact IsOpenEmbedding.of_comp (curvePlaceAdeleLevelMap k F hST)
    (isOpen_curvePlaceAdeleLevel k F T).isOpenEmbedding_subtypeVal
    (isOpen_curvePlaceAdeleLevel k F S).isOpenEmbedding_subtypeVal

theorem exists_mem_curvePlaceAdeleLevel (a : CurvePlaceAdeleRing k F) :
    ∃ S, a ∈ curvePlaceAdeleLevel k F S := by
  classical
  have h := Filter.eventually_cofinite.mp a.property
  refine ⟨h.toFinset, ?_⟩
  intro v hv
  by_contra hn
  exact hv (h.mem_toFinset.mpr hn)

theorem continuous_iff_curvePlaceAdeleLevel {X : Type u} [TopologicalSpace X]
    (f : CurvePlaceAdeleRing k F → X) :
    Continuous f ↔ ∀ S, Continuous (f ∘ (curvePlaceAdeleLevel k F S).subtype) := by
  refine ⟨fun h _ => h.comp continuous_subtype_val, ?_⟩
  intro h
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨S, ha⟩ := exists_mem_curvePlaceAdeleLevel k F a
  exact ((isOpen_curvePlaceAdeleLevel k F S).isOpenEmbedding_subtypeVal.continuousAt_iff).mp
    ((h S).continuousAt (x := ⟨a, ha⟩))

/-- The exact product, transition, exhaustion and final-topology statement. -/
theorem curvePlaceAdeleLevelTopology : CurvePlaceAdeleLevelTopologyStatement.{u} := by
  intro k F _ _ _
  exact ⟨curvePlaceAdeleLevelProductEquiv_isHomeomorph k F,
    fun _ _ hST => curvePlaceAdeleLevelMap_isOpenEmbedding k F hST,
    exists_mem_curvePlaceAdeleLevel k F,
    fun _ _ => continuous_iff_curvePlaceAdeleLevel k F⟩

end Langlands.Global
