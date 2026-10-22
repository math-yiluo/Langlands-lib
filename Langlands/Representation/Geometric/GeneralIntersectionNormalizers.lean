import Langlands.Representation.Geometric.GeneralIntersections

/-! The actual normalizer maps for the Haar corrections in BZ77 section 5.1. -/

namespace Langlands.Geometric.General

universe uG

variable {G : Type uG} [Group G]

/-- Membership in the existing ambient intersection used for the first
Haar correction. -/
@[simp]
theorem mem_correctionSubgroup (U Q : Subgroup G) (w g : G) :
    g ∈ intersectionSource U Q w ↔ g ∈ U ∧ w * g * w⁻¹ ∈ Q := Iff.rfl

theorem correctionSubgroup_eq (U Q : Subgroup G) (w : G) :
    intersectionSource U Q w = U ⊓ conjugate Q w⁻¹ := by
  simp [intersectionSource, conjugate]

/-- The intersection Levi acts on the original radical through its actual
inclusion in the normalizer. -/
def intersectionToRadicalNormalizer (M N U : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) :
    intersectionIn M N w →* Subgroup.normalizer (U : Set G) :=
  (Subgroup.inclusion hMU).comp (intersectionIn M N w).subtype

@[simp]
theorem intersectionToRadicalNormalizer_apply (M N U : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) (m : intersectionIn M N w) :
    (intersectionToRadicalNormalizer M N U w hMU m : G) = m.val.val := rfl

/-- Normalizing each of the two factors implies normalizing their actual
intersection. Conjugation pulls back the second normalizer containment. -/
theorem intersection_mem_correctionNormalizer (M N U Q : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) (hNQ : N ≤ Subgroup.normalizer Q)
    (m : intersectionIn M N w) :
    m.val.val ∈ Subgroup.normalizer (intersectionSource U Q w) := by
  apply Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨hMU m.val.property, ?_⟩
  apply Subgroup.le_normalizer_comap (MulAut.conj w).toMonoidHom
  exact hNQ m.property

/-- The actual inclusion into the normalizer of the correction subgroup.
In BZ77 the second hypothesis is supplied by `N ≤ Q ≤ normalizer Q`. -/
def intersectionToCorrectionNormalizer (M N U Q : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) (hNQ : N ≤ Subgroup.normalizer Q) :
    intersectionIn M N w →* Subgroup.normalizer (intersectionSource U Q w : Set G) where
  toFun m := ⟨m.val.val, intersection_mem_correctionNormalizer M N U Q w hMU hNQ m⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem intersectionToCorrectionNormalizer_apply (M N U Q : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) (hNQ : N ≤ Subgroup.normalizer Q)
    (m : intersectionIn M N w) :
    (intersectionToCorrectionNormalizer M N U Q w hMU hNQ m : G) = m.val.val := rfl

section Topology

variable [TopologicalSpace G]

theorem continuous_intersectionToRadicalNormalizer (M N U : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) :
    Continuous (intersectionToRadicalNormalizer M N U w hMU) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem continuous_intersectionToCorrectionNormalizer (M N U Q : Subgroup G) (w : G)
    (hMU : M ≤ Subgroup.normalizer U) (hNQ : N ≤ Subgroup.normalizer Q) :
    Continuous (intersectionToCorrectionNormalizer M N U Q w hMU hNQ) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable [IsTopologicalGroup G]

theorem isClosed_correctionSubgroup (U Q : Subgroup G) (w : G)
    (hU : IsClosed (U : Set G)) (hQ : IsClosed (Q : Set G)) :
    IsClosed (intersectionSource U Q w : Set G) :=
  hU.inter (hQ.preimage ((continuous_const.mul continuous_id).mul continuous_const))

end Topology

end Langlands.Geometric.General
