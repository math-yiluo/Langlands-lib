import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.Representation.RankinSelberg.Measures
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! Haar normalization by the largest compact subgroup and its transport. -/

noncomputable section

namespace Langlands.BaseChange

open Set MeasureTheory MeasureTheory.Measure
open Langlands.RankinSelberg
open _root_.Topology

universe u v

/-- A group admits a compact open subgroup containing every compact subgroup. -/
abbrev HasLargestCompactOpenSubgroup (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
    ∀ C : Subgroup G, IsCompact (C : Set G) → C ≤ K.toSubgroup

namespace HasLargestCompactOpenSubgroup

variable {G : Type u} {N : Type v} [Group G] [Group N]
  [TopologicalSpace G] [TopologicalSpace N]

/-- The largest compact open subgroup pulls back along a closed group embedding. -/
theorem of_isClosedEmbedding (hN : HasLargestCompactOpenSubgroup N) (f : G →* N)
    (hf : IsClosedEmbedding f) : HasLargestCompactOpenSubgroup G := by
  obtain ⟨K, hK, hmax⟩ := hN
  refine ⟨K.comap f hf.continuous, hf.isProperMap.isCompact_preimage hK, ?_⟩
  intro C hC c hc
  exact hmax (C.map f) (hC.image hf.continuous) ⟨c, hc, rfl⟩

/-- A finite product of such groups has the same property. -/
theorem pi {ι : Type*} [Finite ι] {A : ι → Type*}
    [∀ i, Group (A i)] [∀ i, TopologicalSpace (A i)]
    (h : ∀ i, HasLargestCompactOpenSubgroup (A i)) : HasLargestCompactOpenSubgroup (∀ i, A i) := by
  let K (i : ι) := (h i).choose
  refine ⟨⟨Subgroup.pi univ (fun i => (K i).toSubgroup),
    isOpen_set_pi finite_univ (fun i _ => (K i).isOpen)⟩,
    isCompact_univ_pi (fun i => (h i).choose_spec.1), ?_⟩
  intro C hC c hc i _
  exact (h i).choose_spec.2 (C.map (Pi.evalMonoidHom A i))
    (hC.image (continuous_apply i)) ⟨c, hc, rfl⟩

/-- The integral units in a nonarchimedean local field form its largest compact subgroup. -/
theorem localFieldUnits (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : HasLargestCompactOpenSubgroup Fˣ := by
  let O := (ValuativeRel.valuation F).integer
  have hO : IsOpen (O : Set F) := Valuation.isOpen_integer
  let : T2Space F := localField_t2 F
  refine ⟨integralUnitsOpen O hO, integralUnits_isCompact O, ?_⟩
  intro C hC c hc
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  obtain ⟨m, hm, hmmax⟩ := hC.exists_isMaxOn ⟨1, C.one_mem⟩
    (continuous_norm.comp (Units.continuous_val : Continuous ((↑) : Fˣ → F))).continuousOn
  have hbound (a : Fˣ) (ha : a ∈ C) : ‖(a : F)‖ ≤ 1 := by
    have hpos : 0 < ‖(m : F)‖ := norm_pos_iff.mpr m.ne_zero
    have hmul := hmmax (C.mul_mem hm ha)
    change ‖((m * a : Fˣ) : F)‖ ≤ ‖(m : F)‖ at hmul
    rw [Units.val_mul, norm_mul] at hmul
    exact le_of_mul_le_mul_left (by simpa only [mul_one] using hmul) hpos
  have hmem (a : Fˣ) (ha : a ∈ C) : (a : F) ∈ O := by
    change ValuativeRel.valuation F (a : F) ≤ 1
    simpa using (LocalGalois.localNormedField_le F (a : F) 1).mp (by simpa using hbound a ha)
  exact (mem_integralUnits O c).2 ⟨hmem c hc, hmem c⁻¹ (C.inv_mem hc)⟩

section Measure

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure giving mass one to the largest compact open subgroup. -/
def haar (h : HasLargestCompactOpenSubgroup G) : Measure G :=
  normalizedCompactOpenHaar h.choose h.choose_spec.1

instance (h : HasLargestCompactOpenSubgroup G) : (h.haar).IsHaarMeasure :=
  normalizedCompactOpenHaar_isHaar h.choose h.choose_spec.1

instance (h : HasLargestCompactOpenSubgroup G) : (h.haar).Regular :=
  normalizedCompactOpenHaar_regular h.choose h.choose_spec.1

@[simp] theorem haar_apply_largest (h : HasLargestCompactOpenSubgroup G) :
    h.haar (h.choose : Set G) = 1 :=
  normalizedCompactOpenHaar_self h.choose h.choose_spec.1

variable [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  [LocallyCompactSpace N] [SecondCountableTopology N]

/-- Topological group equivalences preserve the normalization. -/
theorem map_haar (h : HasLargestCompactOpenSubgroup G) (k : HasLargestCompactOpenSubgroup N)
    (e : G ≃ₜ* N) : Measure.map e h.haar = k.haar := by
  have hpre : e ⁻¹' (k.choose : Set N) = (h.choose : Set G) := by
    apply le_antisymm
    · exact h.choose_spec.2 (k.choose.toSubgroup.comap e.toMonoidHom)
        (e.toHomeomorph.isClosedEmbedding.isProperMap.isCompact_preimage k.choose_spec.1)
    · exact Subgroup.map_le_iff_le_comap.mp
        (k.choose_spec.2 (h.choose.toSubgroup.map e.toMonoidHom)
          (h.choose_spec.1.image e.continuous))
  let : (Measure.map e h.haar).IsHaarMeasure := e.isHaarMeasure_map _
  symm
  apply (Measure.haarMeasure_eq_iff (compactOpenPositive k.choose k.choose_spec.1) _).2
  change Measure.map e h.haar (k.choose : Set N) = 1
  have he : Measurable (e : G → N) := e.continuous.measurable
  rw [Measure.map_apply he k.choose.isOpen.measurableSet, hpre,
    haar_apply_largest]

end Measure

end HasLargestCompactOpenSubgroup

end Langlands.BaseChange
