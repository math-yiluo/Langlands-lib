import Langlands.Representation.Conductor.Congruence
import Langlands.Group.GL.Blocks
import Langlands.Group.GL.BlockUnipotent
import Langlands.Group.GL.TwoBlockShape
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Reduction of integral invertible matrices to the residue field

For a local subring `O` of a field `F`, the integral subgroup
`Conductor.integralSubgroup O m` of `GL_{m+1}(F)` maps onto `GL_{m+1}` of the residue field.
Each residue matrix has an integral lift with the same zero and identity entries, so
elements of a block unipotent radical over the residue field lift to integral elements of
the same block unipotent radical over `F`.
-/

noncomputable section

namespace Langlands.GeneralLinear.IntegralReduction

open Matrix IsLocalRing

universe uF

variable {F : Type uF} [Field F] (O : Subring F) (m : ℕ)

/-- Integral invertible matrices, identified with their image in `GL_{m+1}(F)`. -/
def integralEquiv :
    GeneralLinearGroup (Fin (m + 1)) O ≃* Conductor.integralSubgroup O m :=
  MonoidHom.ofInjective (Conductor.integral_map_injective O m)

@[simp]
theorem integralEquiv_apply_val (h : GeneralLinearGroup (Fin (m + 1)) O) (i j : Fin (m + 1)) :
    ((integralEquiv O m h : GeneralLinear (m + 1) F) i j) = (h i j : F) := rfl

theorem integralEquiv_symm_apply_val (g : Conductor.integralSubgroup O m)
    (i j : Fin (m + 1)) :
    (((integralEquiv O m).symm g) i j : F) = (g : GeneralLinear (m + 1) F) i j := by
  conv_rhs => rw [← (integralEquiv O m).apply_symm_apply g]
  rfl

variable [IsLocalRing O]

/-- Reduction of integral invertible matrices modulo the maximal ideal. -/
def reduction :
    Conductor.integralSubgroup O m →* GeneralLinear (m + 1) (ResidueField O) :=
  (GeneralLinearGroup.map (residue O)).comp (integralEquiv O m).symm.toMonoidHom

theorem reduction_apply (g : Conductor.integralSubgroup O m) (i j : Fin (m + 1)) :
    reduction O m g i j = residue O ((integralEquiv O m).symm g i j) := rfl

/-- A set-theoretic section of the residue map fixing `0` and `1`. -/
def residueSection (x : ResidueField O) : O := by
  classical
  exact if x = 0 then 0 else if x = 1 then 1 else (residue_surjective x).choose

@[simp]
theorem residue_residueSection (x : ResidueField O) : residue O (residueSection O x) = x := by
  classical
  unfold residueSection
  split_ifs with h0 h1
  · rw [h0, map_zero]
  · rw [h1, map_one]
  · exact (residue_surjective x).choose_spec

@[simp]
theorem residueSection_zero : residueSection O 0 = 0 := by
  simp [residueSection]

@[simp]
theorem residueSection_one : residueSection O 1 = 1 := by
  classical
  unfold residueSection
  simp

/-- The entrywise lift of a residue matrix. -/
def liftMatrix (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ResidueField O)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) O :=
  A.map (residueSection O)

theorem map_residue_liftMatrix (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ResidueField O)) :
    (liftMatrix O m A).map (residue O) = A := by
  ext i j
  simp [liftMatrix]

theorem isUnit_det_liftMatrix (γ : GeneralLinear (m + 1) (ResidueField O)) :
    IsUnit (liftMatrix O m γ.val).det := by
  apply isUnit_of_map_unit (residue O)
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_residue_liftMatrix]
  exact (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit

/-- The integral invertible lift of a residue invertible matrix. -/
def liftUnit (γ : GeneralLinear (m + 1) (ResidueField O)) : GeneralLinearGroup (Fin (m + 1)) O :=
  nonsingInvUnit _ (isUnit_det_liftMatrix O m γ)

@[simp]
theorem liftUnit_apply (γ : GeneralLinear (m + 1) (ResidueField O)) (i j : Fin (m + 1)) :
    liftUnit O m γ i j = residueSection O (γ i j) := rfl

/-- The lift of a residue invertible matrix to the integral subgroup of `GL_{m+1}(F)`. -/
def lift (γ : GeneralLinear (m + 1) (ResidueField O)) : Conductor.integralSubgroup O m :=
  integralEquiv O m (liftUnit O m γ)

@[simp]
theorem lift_apply (γ : GeneralLinear (m + 1) (ResidueField O)) (i j : Fin (m + 1)) :
    ((lift O m γ : GeneralLinear (m + 1) F) i j) = (residueSection O (γ i j) : F) := rfl

@[simp]
theorem reduction_lift (γ : GeneralLinear (m + 1) (ResidueField O)) :
    reduction O m (lift O m γ) = γ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [reduction_apply, lift, MulEquiv.symm_apply_apply]
  simp

/-- Reduction is surjective. -/
theorem reduction_surjective : Function.Surjective (reduction O m) :=
  fun γ => ⟨lift O m γ, reduction_lift O m γ⟩

/-- The lift of an element of a block unipotent radical over the residue field lies in the
same block unipotent radical over `F`. -/
theorem lift_mem_unipotentSubgroup (B : BlockShape (m + 1))
    {γ : GeneralLinear (m + 1) (ResidueField O)} (hγ : γ ∈ B.unipotentSubgroup (ResidueField O)) :
    (lift O m γ : GeneralLinear (m + 1) F) ∈ B.unipotentSubgroup F := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hγ ⊢
  obtain ⟨hP, hD⟩ := hγ
  rw [BlockShape.mem_parabolic_iff] at hP
  refine ⟨?_, ?_⟩
  · rw [BlockShape.mem_parabolic_iff]
    intro i j a b hij
    rw [lift_apply, hP i j a b hij, residueSection_zero]
    rfl
  · intro i a b
    rw [lift_apply, hD i a b]
    split_ifs
    · rw [residueSection_one]; rfl
    · rw [residueSection_zero]; rfl

end Langlands.GeneralLinear.IntegralReduction
