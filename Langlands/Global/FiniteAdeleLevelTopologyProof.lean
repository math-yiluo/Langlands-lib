import Langlands.Global.FiniteAdeleLevelTopologyStatement

/-! # Proof of the topology of actual finite-adelic level rings -/

noncomputable section

universe u

open IsDedekindDomain Topology
open scoped RestrictedProduct

namespace Langlands.Global

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

theorem continuous_finiteAdeleLevelProductEquiv (S : Finset (HeightOneSpectrum R)) :
    Continuous (finiteAdeleLevelProductEquiv R K S) := by
  change Continuous (fun a : finiteAdeleLevel R K S =>
    ((fun v : {v : HeightOneSpectrum R // v ∈ S} =>
      (a : FiniteAdeleRing R K) v.1),
      fun v : {v : HeightOneSpectrum R // v ∉ S} =>
        (⟨(a : FiniteAdeleRing R K) v.1, a.property v.1 v.property⟩ :
          v.1.adicCompletionIntegers K)))
  apply Continuous.prodMk
  · exact continuous_pi (fun v =>
      (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val)
  · apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val

theorem continuous_finiteAdeleLevelAssemble (S : Finset (HeightOneSpectrum R)) :
    Continuous (finiteAdeleLevelAssemble R K S) := by
  classical
  let P := (∀ v : {v : HeightOneSpectrum R // v ∈ S}, v.1.adicCompletion K) ×
    (∀ v : {v : HeightOneSpectrum R // v ∉ S}, v.1.adicCompletionIntegers K)
  let g : P → Πʳ v : HeightOneSpectrum R,
      [v.adicCompletion K, v.adicCompletionIntegers K]_[
        Filter.principal (S : Set (HeightOneSpectrum R))ᶜ] :=
    fun p => ⟨fun v => (finiteAdeleLevelAssemble R K S p : FiniteAdeleRing R K) v,
      Filter.eventually_principal.mpr (fun v hv =>
        (finiteAdeleLevelAssemble R K S p).property v hv)⟩
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    by_cases hv : v ∈ S
    · change Continuous (fun p : P =>
        (if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩).val :
          v.adicCompletion K))
      simpa only [dite_eq_left hv, Function.comp_def] using
        (continuous_apply (⟨v, hv⟩ : {v : HeightOneSpectrum R // v ∈ S})).comp
          (show Continuous (fun p : P => p.1) from continuous_fst)
    · change Continuous (fun p : P =>
        (if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩).val :
          v.adicCompletion K))
      simpa only [dite_eq_right hv, Function.comp_def] using continuous_subtype_val.comp
        ((continuous_apply (⟨v, hv⟩ : {v : HeightOneSpectrum R // v ∉ S})).comp
          (show Continuous (fun p : P => p.2) from continuous_snd))
  have hS : Filter.cofinite ≤ Filter.principal (S : Set (HeightOneSpectrum R))ᶜ := by simp
  have h : Continuous (fun p : P =>
      (finiteAdeleLevelAssemble R K S p : FiniteAdeleRing R K)) :=
    (RestrictedProduct.continuous_inclusion hS).comp hg
  exact h.subtype_mk _

theorem finiteAdeleLevelProductEquiv_isHomeomorph (S : Finset (HeightOneSpectrum R)) :
    IsHomeomorph (finiteAdeleLevelProductEquiv R K S) :=
  (show finiteAdeleLevel R K S ≃ₜ _ from
    { toEquiv := (finiteAdeleLevelProductEquiv R K S).toEquiv
      continuous_toFun := continuous_finiteAdeleLevelProductEquiv R K S
      continuous_invFun := continuous_finiteAdeleLevelAssemble R K S }).isHomeomorph

theorem finiteAdeleLevelMap_isOpenEmbedding {S T : Finset (HeightOneSpectrum R)}
    (hST : S ⊆ T) : IsOpenEmbedding (finiteAdeleLevelMap R K hST) := by
  exact IsOpenEmbedding.of_comp (finiteAdeleLevelMap R K hST)
    (isOpen_finiteAdeleLevel R K T).isOpenEmbedding_subtypeVal
    (isOpen_finiteAdeleLevel R K S).isOpenEmbedding_subtypeVal

theorem exists_mem_finiteAdeleLevel (a : FiniteAdeleRing R K) :
    ∃ S, a ∈ finiteAdeleLevel R K S := by
  classical
  have h := Filter.eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers
  refine ⟨h.toFinset, ?_⟩
  intro v hv
  by_contra hn
  exact hv (h.mem_toFinset.mpr hn)

theorem continuous_iff_finiteAdeleLevel {X : Type u} [TopologicalSpace X]
    (f : FiniteAdeleRing R K → X) :
    Continuous f ↔ ∀ S, Continuous (f ∘ (finiteAdeleLevel R K S).subtype) := by
  refine ⟨fun h _ => h.comp continuous_subtype_val, ?_⟩
  intro h
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨S, ha⟩ := exists_mem_finiteAdeleLevel R K a
  exact ((isOpen_finiteAdeleLevel R K S).isOpenEmbedding_subtypeVal.continuousAt_iff).mp
    ((h S).continuousAt (x := ⟨a, ha⟩))

/-- The exact product, transition, exhaustion and final-topology statement. -/
theorem finiteAdeleLevelTopology : FiniteAdeleLevelTopologyStatement.{u} := by
  intro R K _ _ _ _ _
  exact ⟨finiteAdeleLevelProductEquiv_isHomeomorph R K,
    fun _ _ hST => finiteAdeleLevelMap_isOpenEmbedding R K hST,
    exists_mem_finiteAdeleLevel R K,
    fun _ _ => continuous_iff_finiteAdeleLevel R K⟩

end Langlands.Global
