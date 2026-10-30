import Langlands.Representation.Classification.SegmentFullJacquetSplitting
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Classification.SegmentJacquetReversal
import Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Group.GL.BlockIwahoriBasis

/-!
# Nonzero maps out of and into the Jacquet module of a segment constituent

First adjointness turns an embedding of `π` into the increasing segment induction
into a nonzero map from the Jacquet module of `π` to the increasing tensor.
Second adjointness, followed by the identification of the opposite Jacquet
module with the block-reversed upper one, turns a quotient map onto `π` into a
nonzero map from the block-reversed increasing tensor to the Jacquet module.
-/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Geometric CuspidalSupport OppositeCuspidalJacquetFiltration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- First adjointness: a nonzero map from `π` into the segment induction gives a
nonzero map from the Jacquet module of `π` to the increasing segment tensor. -/
theorem exists_jacquet_to_tensor_ne_zero {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (j : letI := T.topology
      π.representation.IntertwiningMap (T.segmentInduced A m hr).representation)
    (hj : j ≠ 0) :
    letI := T.topology
    ∃ f : ((T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj π).representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation, f ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopology (m * r)
  let := T.generalLinearTopologicalGroup (m * r)
  exact ⟨Parabolic.FirstAdjointness.equiv T (BlockShape.uniform m r hr) π.isSmooth j,
    (LinearEquiv.map_ne_zero_iff _).mpr hj⟩

/-- A quotient of the segment induction of an admissible representation is
admissible. -/
theorem isAdmissible_of_segmentQuotient {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hA : letI := T.topology
      IsAdmissible A.representation)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (q : letI := T.topology
      (T.segmentInduced A m hr).representation.IntertwiningMap π.representation)
    (hq : Function.Surjective q) :
    letI := T.topology
    IsAdmissible π.representation := by
  let := T.topology
  let := T.generalLinearTopology (m * r)
  let := T.generalLinearTopologicalGroup (m * r)
  have hI := (Classification.segmentInductionAdmissibility F T m hr A hA).2.2.1
  refine Unramified.SphericalExistence.isAdmissible_of_surjective ?_ q hq hI
  intro H
  obtain ⟨K, hK, hKH, -⟩ :=
    (BlockShape.uniform m r hr).exists_compactOpenSubgroup_hasBlockIwahoriFactorization T
      (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, hKH⟩

/-- Reversal of the block order of the uniform Levi `GL_r × ⋯ × GL_r`. -/
def uniformReverse (m r : ℕ) (hr : 0 < r) :
    (BlockShape.uniform m r hr).Levi F.Carrier →* (BlockShape.uniform m r hr).Levi F.Carrier where
  toFun x i := x i.rev
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem uniformReverse_apply (m r : ℕ) (hr : 0 < r)
    (x : (BlockShape.uniform m r hr).Levi F.Carrier) (i : Fin m) :
    uniformReverse F m r hr x i = x i.rev := rfl

/-- Second adjointness: a nonzero quotient map from the segment induction onto an
admissible `π` gives a nonzero map from the block-reversed increasing segment
tensor to the Jacquet module of `π`. -/
theorem exists_reversedTensor_to_jacquet_ne_zero {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hA : letI := T.topology
      IsAdmissible A.representation)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (q : letI := T.topology
      (T.segmentInduced A m hr).representation.IntertwiningMap π.representation)
    (hq : Function.Surjective q) (hq0 : q ≠ 0) :
    letI := T.topology
    ∃ g : Representation.IntertwiningMap
        ((FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation.comp
          (uniformReverse F m r hr))
        ((T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj π).representation,
      g ≠ 0 := by
  let := T.topology
  let β := BlockShape.uniform m r hr
  have hadm := Classification.segmentInductionAdmissibility F T m hr A hA
  have hπ := isAdmissible_of_segmentQuotient F T hr A hA π q hq
  obtain ⟨E, -, -⟩ := (Parabolic.normalizedSecondAdjointness.{uF, uV, max uF uV}).1 p F T
    (m * r) (Nat.mul_pos hm hr) β
  let σ : Rep.{uV} ℂ (β.Levi F.Carrier) :=
    Rep.of (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation
  let P : Rep.{max uF uV} ℂ (GeneralLinear (m * r) F.Carrier) := Rep.of π.representation
  let f₀ := E σ P hadm.1 hπ q
  have hf₀ : f₀ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hq0
  let f₁ := (oppositeJacquetReverseEquiv T β P).symm.toIntertwiningMap.comp f₀
  have hf₁ : f₁ ≠ 0 := by
    intro h
    apply hf₀
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : f₁ v = 0 := by rw [h]; rfl
    have key : f₀ v = (oppositeJacquetReverseEquiv T β P).toLinearEquiv (f₁ v) := by
      change f₀ v = (oppositeJacquetReverseEquiv T β P).toLinearEquiv
        ((oppositeJacquetReverseEquiv T β P).toLinearEquiv.symm (f₀ v))
      rw [LinearEquiv.apply_symm_apply]
    rw [hv, map_zero] at key
    exact key
  refine ⟨⟨f₁.toLinearMap, fun x => ?_⟩, ?_⟩
  · have h := f₁.isIntertwining' (uniformReverse F m r hr x)
    have hx : leviReverseEquiv β (uniformReverse F m r hr x) = x := by
      funext i
      change x i.rev.rev = x i
      rw [Fin.rev_rev]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx] at h
    exact h
  · intro h
    apply hf₁
    have h' := congrArg Representation.IntertwiningMap.toLinearMap h
    exact Representation.IntertwiningMap.ext h'

end Langlands.SegmentFullJacquet
