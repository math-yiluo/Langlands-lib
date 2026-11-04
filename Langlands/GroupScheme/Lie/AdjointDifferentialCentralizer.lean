import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.ElementCentralizerMatrix
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.SemisimpleElement

/-! # The actual adjoint differential and tangent centralizers -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

variable {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]

/-- A first-order matrix fixes a constant vector exactly when its tangent
matrix annihilates the original vector. -/
theorem matrixUnit_mulVec_constant_eq_iff (M : Matrix n n A) (v : n → A) :
    (matrixUnit M : Matrix n n (DualNumber A)) *ᵥ
      (fun i => TrivSqZeroExt.inl (v i)) = (fun i => TrivSqZeroExt.inl (v i)) ↔
      M *ᵥ v = 0 := by
  have hε : epsilonMatrix M *ᵥ (fun i => TrivSqZeroExt.inl (v i)) =
      fun i => TrivSqZeroExt.inr ((M *ᵥ v) i) := by
    funext i
    apply TrivSqZeroExt.ext <;>
      simp [Matrix.mulVec, dotProduct, epsilonMatrix,
        TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]
  rw [matrixUnit_val, Matrix.add_mulVec, Matrix.one_mulVec, hε]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun w : n → DualNumber A => (w i).snd) h
    simpa using hi
  · intro h
    rw [h]
    simp
    rfl

end Langlands.GroupScheme.GeneralLinear.DualNumber

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

/-- The genuine adjoint representation differential, as a linear family of
endomorphisms of the finite coordinate module. -/
def adjointDifferentialFamily :
    Additive (lieKernel G R) →ₗ[R] Module.End R (Fin d → R) :=
  Matrix.toLin'.toLinearMap.comp ((adjointRepresentation c).kernelDifferential R)

@[simp]
theorem adjointDifferentialFamily_apply (X : lieKernel G R) :
    adjointDifferentialFamily c (Additive.ofMul X) =
      Matrix.toLin' ((adjointRepresentation c).tangentMatrix R X) := rfl

/-- Tangent membership in the all-test centralizer is the vanishing of the
actual adjoint differential on the fixed element's coordinates. -/
theorem mem_elementCentralizerLie_iff_adjointDifferential
    (X Y : lieKernel G R) :
    Additive.ofMul Y ∈ elementCentralizerLie G X ↔
      adjointDifferentialFamily c (Additive.ofMul Y)
        (c.equiv (.of R R) (Additive.ofMul X)) = 0 := by
  change Y.val ∈ (elementCentralizer G X).carrier _ ↔ _
  rw [mem_elementCentralizer_adjoint_iff]
  rw [← (c.equiv (.of R (DualNumber R))).injective.eq_iff,
    ← adjointRepresentation_affineAction]
  have hc := c.naturality
    (CommAlgCat.ofHom (Algebra.ofId R (DualNumber R))) (Additive.ofMul X)
  change c.equiv (.of R (DualNumber R))
      (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) (Additive.ofMul X)) =
    (fun i => TrivSqZeroExt.inl (c.equiv (.of R R) (Additive.ofMul X) i)) at hc
  rw [hc, MatrixRepresentation.affineAction_apply,
    MatrixRepresentation.affineMatrix_lieKernel]
  exact matrixUnit_mulVec_constant_eq_iff _ _

variable {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {e : ℕ} (cH : FiniteCoordinates H e)

local instance adjointDifferentialCentralizerKernelCommGroup : CommGroup (lieKernel H k) := lieKernelCommGroup H
local instance adjointDifferentialCentralizerKernelModule : Module k (Additive (lieKernel H k)) := lieKernelModule H

/-- In intrinsic finite coordinates, a tangent centralizer is the kernel of
its element's own adjoint differential. -/
theorem mem_elementCentralizerLie_iff_adjointDifferential_self
    (X Y : lieKernel H k) :
    Additive.ofMul Y ∈ elementCentralizerLie H X ↔
      adjointDifferentialFamily cH (Additive.ofMul X)
        (cH.equiv (.of (CommRingCat.of k) k) (Additive.ofMul Y)) = 0 := by
  rw [mem_elementCentralizerLie_comm]
  exact mem_elementCentralizerLie_iff_adjointDifferential cH Y X

/-- The full tangent centralizer is equivalent to a zero actual adjoint
endomorphism, including in dimension zero. -/
theorem elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero
    (X : lieKernel H k) :
    elementCentralizerLie H X = ⊤ ↔
      adjointDifferentialFamily cH (Additive.ofMul X) = 0 := by
  rw [Submodule.eq_top_iff']
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    obtain ⟨Y, rfl⟩ := (cH.equiv (.of (CommRingCat.of k) k)).surjective v
    exact (mem_elementCentralizerLie_iff_adjointDifferential_self cH X Y.toMul).mp (h Y)
  · intro h Y
    apply (mem_elementCentralizerLie_iff_adjointDifferential_self cH X Y.toMul).mpr
    rw [h, LinearMap.zero_apply]

/-- A representation-semisimple Lie element with proper tangent centralizer
has a nonnilpotent actual adjoint differential over the original field. -/
theorem not_isNilpotent_adjointDifferential_of_semisimple
    {X : lieKernel H k} (hX : IsSemisimpleElement H X)
    (hnoncentral : elementCentralizerLie H X ≠ ⊤) :
    ¬ IsNilpotent (adjointDifferentialFamily cH (Additive.ofMul X)) := by
  intro hn
  have hnM : IsNilpotent ((adjointRepresentation cH).tangentMatrix k X) := by
    change IsNilpotent
      (Matrix.toLinAlgEquiv' ((adjointRepresentation cH).tangentMatrix k X)) at hn
    have hh := hn.map Matrix.toLinAlgEquiv'.symm
    simpa only [AlgEquiv.symm_apply_apply] using hh
  have hnK := hnM.map ((algebraMap k (AlgebraicClosure k)).mapMatrix)
  have hnE := hnK.map Matrix.toLinAlgEquiv'
  have hs := hX e (adjointRepresentation cH)
  have hz := Module.End.eq_zero_of_isNilpotent_isSemisimple hnE hs
  have hzM : ((adjointRepresentation cH).tangentMatrix k X).map
      (algebraMap k (AlgebraicClosure k)) = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    simpa only [map_zero, RingHom.mapMatrix_apply] using hz
  have hM : (adjointRepresentation cH).tangentMatrix k X = 0 := by
    ext i j
    apply (algebraMap k (AlgebraicClosure k)).injective
    simpa using congrArg (fun M => M i j) hzM
  apply hnoncentral
  apply (elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero cH X).mpr
  rw [adjointDifferentialFamily_apply, hM, map_zero]

end Langlands.GroupScheme.Lie
