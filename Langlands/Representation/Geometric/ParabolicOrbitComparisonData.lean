import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Geometric.BlockSixDecomposableProof
import Langlands.Representation.Geometric.BlockIntersectionSplitting

/-! Actual subgroup bridges for the local parabolic-orbit comparison. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uF

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The actual stabilizer inside the target parabolic. -/
abbrev parabolicOrbitStabilizer : Subgroup (C.parabolic F) :=
  orbitStabilizer (B.parabolic F) (C.parabolic F) (permutation n F w)

/-- The subgroup through which induction in stages factors: the inverse image
of the target intersection parabolic under the actual target Levi projection. -/
def parabolicOrbitStages : Subgroup (C.parabolic F) :=
  (sourceParabolic F C B w⁻¹).comap (C.leviProjection F)

theorem parabolicOrbitStages_kernel_le :
    (C.leviProjection F).ker ≤ parabolicOrbitStages F B C w := by
  intro q hq
  change C.leviProjection F q ∈ sourceParabolic F C B w⁻¹
  rw [show C.leviProjection F q = 1 from hq]
  exact (sourceParabolic F C B w⁻¹).one_mem

@[simp]
theorem parabolicOrbitStages_comap_section :
    (parabolicOrbitStages F B C w).comap (C.leviInParabolic F) =
      sourceParabolic F C B w⁻¹ := by
  ext l
  change C.leviProjection F (C.leviInParabolic F l) ∈ sourceParabolic F C B w⁻¹ ↔
    l ∈ sourceParabolic F C B w⁻¹
  rw [C.leviProjection_section]

@[simp]
theorem parabolicOrbitStabilizer_comap_section :
    (parabolicOrbitStabilizer F B C w).comap (C.leviInParabolic F) =
      sourceParabolic F C B w⁻¹ := by
  ext l
  change (permutation n F w)⁻¹ * C.leviEmbedding F l *
      ((permutation n F w)⁻¹)⁻¹ ∈ B.parabolic F ↔
    permutation n F w⁻¹ * C.leviEmbedding F l *
      (permutation n F w⁻¹)⁻¹ ∈ B.parabolic F
  simp only [map_inv, inv_inv]

/-- The first literal decomposability condition puts the target diagonal block
of every stabilizer element back into the same stabilizer. -/
theorem parabolicOrbitStabilizer_le_stages :
    parabolicOrbitStabilizer F B C w ≤ parabolicOrbitStages F B C w := by
  intro q hq
  have hm := blockIntersection_leviProjection_mem F C
    (General.conjugate (B.parabolic F) (permutation n F w))
    (blockParabolic_sixDecomposable F B C w).1
    ⟨q.val, hq, q.property⟩
  change permutation n F w⁻¹ * C.leviEmbedding F (C.leviProjection F q) *
    (permutation n F w⁻¹)⁻¹ ∈ B.parabolic F
  simpa only [General.mem_conjugate, map_inv, inv_inv] using hm

/-- The target section over the intersection parabolic lands in the actual
stabilizer, as required by the split-kernel comparison. -/
theorem parabolicOrbitStages_section_mem
    (l : (parabolicOrbitStages F B C w).comap (C.leviInParabolic F)) :
    C.leviInParabolic F l.val ∈ parabolicOrbitStabilizer F B C w := by
  have hl : l.val ∈ sourceParabolic F C B w⁻¹ := by
    simpa only [parabolicOrbitStages_comap_section] using l.property
  change (C.leviInParabolic F l.val) ∈
    (parabolicOrbitStabilizer F B C w)
  change l.val ∈ (parabolicOrbitStabilizer F B C w).comap (C.leviInParabolic F)
  rw [parabolicOrbitStabilizer_comap_section]
  exact hl

/-- The inducing coefficient map is inverse conjugation followed by the actual
source diagonal-block projection. -/
def parabolicOrbitToSourceLevi :
    parabolicOrbitStabilizer F B C w →* B.Levi F :=
  (B.leviProjection F).comp
    (stabilizerToInducing (B.parabolic F) (C.parabolic F) (permutation n F w))

/-- The actual intersection of the stabilizer and the target radical, as a
subgroup of that radical. -/
abbrev parabolicOrbitRadicalIntersection : Subgroup (C.unipotentRadical F) :=
  (parabolicOrbitStabilizer F B C w).comap (C.unipotentRadical F).subtype

theorem parabolicOrbitRadicalToSource_mem
    (j : parabolicOrbitRadicalIntersection F B C w) :
    parabolicOrbitToSourceLevi F B C w
      ((C.unipotentRadical F).subtype.subgroupComap
        (parabolicOrbitStabilizer F B C w) j) ∈ sourceUnipotent F B C w := by
  let q := stabilizerToInducing (B.parabolic F) (C.parabolic F) (permutation n F w)
    ((C.unipotentRadical F).subtype.subgroupComap
      (parabolicOrbitStabilizer F B C w) j)
  have hq : q.val ∈
      General.conjugate (C.unipotentSubgroup F) (permutation n F w)⁻¹ := by
    apply (General.mem_conjugate _ _ _).mpr
    change ((permutation n F w)⁻¹)⁻¹ *
      ((permutation n F w)⁻¹ * j.val.val.val * permutation n F w) *
      (permutation n F w)⁻¹ ∈ C.unipotentSubgroup F
    simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      using (show j.val.val.val ∈ C.unipotentSubgroup F from
        ⟨j.val.val, j.val.property, rfl⟩)
  have hm := blockIntersection_leviProjection_mem F B
    (General.conjugate (C.unipotentSubgroup F) (permutation n F w)⁻¹)
    (blockParabolic_sixDecomposable F B C w).2.2.2.2.2
    ⟨q.val, hq, q.property⟩
  change permutation n F w * B.leviEmbedding F (B.leviProjection F q) *
    (permutation n F w)⁻¹ ∈ C.unipotentSubgroup F
  simpa only [General.mem_conjugate, inv_inv] using hm

/-- The actual surjection from the radical stabilizer intersection to the
unipotent subgroup whose coinvariants define the source refined Jacquet module. -/
def parabolicOrbitRadicalToSource :
    parabolicOrbitRadicalIntersection F B C w →* sourceUnipotent F B C w :=
  ((parabolicOrbitToSourceLevi F B C w).comp
    ((C.unipotentRadical F).subtype.subgroupComap
      (parabolicOrbitStabilizer F B C w))).codRestrict _
        (parabolicOrbitRadicalToSource_mem F B C w)

/-- Forward conjugation of an embedded source unipotent element is an element
of the actual target radical. -/
def sourceUnipotentToTargetRadical :
    sourceUnipotent F B C w →* C.unipotentRadical F where
  toFun m := ⟨⟨conjugatedLeviMap F B w m.val,
    ((C.mem_unipotentSubgroup_iff F _).mp m.property).1⟩, by
      obtain ⟨q, hq, he⟩ := m.property
      exact (show q = ⟨conjugatedLeviMap F B w m.val,
        ((C.mem_unipotentSubgroup_iff F _).mp m.property).1⟩
        from Subtype.ext he) ▸ hq⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one ((conjugatedLeviMap F B w).comp (sourceUnipotent F B C w).subtype)
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (conjugatedLeviMap F B w) a.val b.val

theorem sourceUnipotentToTargetRadical_mem
    (m : sourceUnipotent F B C w) :
    sourceUnipotentToTargetRadical F B C w m ∈
      parabolicOrbitRadicalIntersection F B C w := by
  change (permutation n F w)⁻¹ *
    (permutation n F w * B.leviEmbedding F m.val * (permutation n F w)⁻¹) *
      ((permutation n F w)⁻¹)⁻¹ ∈ B.parabolic F
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one,
    B.leviInParabolic_val]
    using (B.leviInParabolic F m.val).property

/-- A canonical group-homomorphic section of the radical-intersection map. -/
def parabolicOrbitRadicalSourceSection :
    sourceUnipotent F B C w →* parabolicOrbitRadicalIntersection F B C w :=
  (sourceUnipotentToTargetRadical F B C w).codRestrict _
    (sourceUnipotentToTargetRadical_mem F B C w)

@[simp]
theorem parabolicOrbitRadicalToSource_section
    (m : sourceUnipotent F B C w) :
    parabolicOrbitRadicalToSource F B C w
      (parabolicOrbitRadicalSourceSection F B C w m) = m := by
  apply Subtype.ext
  change B.leviProjection F _ = m.val
  have h : stabilizerToInducing (B.parabolic F) (C.parabolic F) (permutation n F w)
      ((C.unipotentRadical F).subtype.subgroupComap
        (parabolicOrbitStabilizer F B C w)
          (parabolicOrbitRadicalSourceSection F B C w m)) =
      B.leviInParabolic F m.val := by
    apply Subtype.ext
    change (permutation n F w)⁻¹ *
      (permutation n F w * B.leviEmbedding F m.val * (permutation n F w)⁻¹) *
        ((permutation n F w)⁻¹)⁻¹ = B.leviEmbedding F m.val
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [h, B.leviProjection_section]

theorem parabolicOrbitRadicalToSource_surjective :
    Function.Surjective (parabolicOrbitRadicalToSource F B C w) := by
  intro m
  exact ⟨parabolicOrbitRadicalSourceSection F B C w m,
    parabolicOrbitRadicalToSource_section F B C w m⟩

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_parabolicOrbitToSourceLevi :
    Continuous (parabolicOrbitToSourceLevi F B C w) :=
  (B.leviProjectionContinuous F).continuous.comp
    (((continuous_const.mul
      (continuous_subtype_val.comp continuous_subtype_val)).mul
        continuous_const).subtype_mk _)

theorem continuous_parabolicOrbitRadicalToSource :
    Continuous (parabolicOrbitRadicalToSource F B C w) :=
  ((continuous_parabolicOrbitToSourceLevi F B C w).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _

theorem continuous_parabolicOrbitRadicalSourceSection :
    Continuous (parabolicOrbitRadicalSourceSection F B C w) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_const.mul
    ((B.leviEmbeddingContinuous F).continuous.comp continuous_subtype_val)).mul
      continuous_const

variable [T2Space F]

theorem isClosed_parabolicOrbitStabilizer :
    IsClosed (parabolicOrbitStabilizer F B C w : Set (C.parabolic F)) :=
  (B.isClosed_parabolic F).preimage
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem isClosed_parabolicOrbitStages :
    IsClosed (parabolicOrbitStages F B C w : Set (C.parabolic F)) :=
  (B.isClosed_parabolic F).preimage
    ((continuous_const.mul
      ((C.leviEmbeddingContinuous F).continuous.comp
        (C.leviProjectionContinuous F).continuous)).mul continuous_const)

theorem isClosed_parabolicOrbitRadicalIntersection :
    IsClosed (parabolicOrbitRadicalIntersection F B C w :
      Set (C.unipotentRadical F)) :=
  (isClosed_parabolicOrbitStabilizer F B C w).preimage continuous_subtype_val

end Topology

end Langlands.Geometric
