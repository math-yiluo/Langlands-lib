import Langlands.Global.NumberFieldAdeleLevelTopologyStatement
import Langlands.Global.FiniteAdeleLevelTopologyProof

/-! # Proof of the topology of actual full number-field adelic levels -/

noncomputable section

universe u

open Topology

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

theorem continuous_numberFieldAdeleLevelSplit (S : Finset (FinitePlace K)) :
    Continuous (numberFieldAdeleLevelSplit K S) := by
  change Continuous (fun a : numberFieldAdeleLevel K S =>
    (a.val.1, (⟨a.val.2, a.property⟩ :
      finiteAdeleLevel (NumberField.RingOfIntegers K) K S)))
  apply Continuous.prodMk
  · exact continuous_fst.comp continuous_subtype_val
  · apply Continuous.subtype_mk
    exact continuous_snd.comp continuous_subtype_val

theorem continuous_numberFieldAdeleLevelSplit_symm (S : Finset (FinitePlace K)) :
    Continuous (numberFieldAdeleLevelSplit K S).symm :=
  (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem numberFieldAdeleLevelProductEquiv_isHomeomorph (S : Finset (FinitePlace K)) :
    IsHomeomorph (numberFieldAdeleLevelProductEquiv K S) := by
  let hSplit : numberFieldAdeleLevel K S ≃ₜ
      InfiniteAdeles K × finiteAdeleLevel (NumberField.RingOfIntegers K) K S :=
    { toEquiv := (numberFieldAdeleLevelSplit K S).toEquiv
      continuous_toFun := continuous_numberFieldAdeleLevelSplit K S
      continuous_invFun := continuous_numberFieldAdeleLevelSplit_symm K S }
  let hFinite :=
    (finiteAdeleLevelProductEquiv_isHomeomorph (NumberField.RingOfIntegers K) K S).homeomorph
  exact (hSplit.trans ((Homeomorph.refl (InfiniteAdeles K)).prodCongr hFinite)).isHomeomorph

theorem numberFieldAdeleLevelMap_isOpenEmbedding {S T : Finset (FinitePlace K)}
    (hST : S ⊆ T) : IsOpenEmbedding (numberFieldAdeleLevelMap K hST) := by
  exact IsOpenEmbedding.of_comp (numberFieldAdeleLevelMap K hST)
    (isOpen_numberFieldAdeleLevel K T).isOpenEmbedding_subtypeVal
    (isOpen_numberFieldAdeleLevel K S).isOpenEmbedding_subtypeVal

theorem exists_mem_numberFieldAdeleLevel (a : Adeles K) :
    ∃ S, a ∈ numberFieldAdeleLevel K S := by
  obtain ⟨S, hS⟩ := exists_mem_finiteAdeleLevel (NumberField.RingOfIntegers K) K a.2
  exact ⟨S, hS⟩

theorem continuous_iff_numberFieldAdeleLevel {X : Type u} [TopologicalSpace X]
    (f : Adeles K → X) :
    Continuous f ↔ ∀ S, Continuous (f ∘ (numberFieldAdeleLevel K S).subtype) := by
  refine ⟨fun h _ => h.comp continuous_subtype_val, ?_⟩
  intro h
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨S, ha⟩ := exists_mem_numberFieldAdeleLevel K a
  exact ((isOpen_numberFieldAdeleLevel K S).isOpenEmbedding_subtypeVal.continuousAt_iff).mp
    ((h S).continuousAt (x := ⟨a, ha⟩))

/-- The exact product, transition, exhaustion and final-topology statement. -/
theorem numberFieldAdeleLevelTopology : NumberFieldAdeleLevelTopologyStatement.{u} := by
  intro K _ _
  exact ⟨numberFieldAdeleLevelProductEquiv_isHomeomorph K,
    fun _ _ hST => numberFieldAdeleLevelMap_isOpenEmbedding K hST,
    exists_mem_numberFieldAdeleLevel K,
    fun _ _ => continuous_iff_numberFieldAdeleLevel K⟩

end Langlands.Global
