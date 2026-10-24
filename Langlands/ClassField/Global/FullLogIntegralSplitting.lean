import Langlands.ClassField.Global.AugmentedFullLogUnitLattice

/-! # Integral splitting and arithmetic actions on the full logarithmic lattices -/

noncomputable section

open NumberField
open scoped Classical

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [NumberField E]

/-- Add an integer constant vector to an actual logarithmic unit-lattice vector. -/
def fullLogLatticeAssemble :
    (fullLogUnitLattice E × ℤ) →ₗ[ℤ] augmentedFullLogUnitLattice E where
  toFun x := ⟨(x.1 : fullLogHyperplane E) + fullLogConstant E (x.2 : ℝ),
    (mem_augmentedFullLogUnitLattice_iff E _).mpr ⟨x.1, x.2, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Int.cast_add, map_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    funext w
    simp [fullLogConstant, zsmul_eq_mul]

@[simp] theorem fullLogLatticeAssemble_apply (x : fullLogUnitLattice E × ℤ) :
    (fullLogLatticeAssemble E x : InfinitePlace E → ℝ) =
      (x.1 : fullLogHyperplane E) + fullLogConstant E (x.2 : ℝ) := rfl

theorem fullLogLatticeAssemble_bijective : Function.Bijective (fullLogLatticeAssemble E) := by
  constructor
  · intro x y h
    have hv := congrArg (fun z : augmentedFullLogUnitLattice E =>
      (z : InfinitePlace E → ℝ)) h
    have hmean := congrArg (fullLogMean E) hv
    have hz : x.2 = y.2 := by
      simpa only [fullLogLatticeAssemble_apply, map_add, fullLogMean_hyperplane,
        fullLogMean_constant, zero_add, Int.cast_inj] using hmean
    have hcenter := congrArg (fullLogCentered E) hv
    have hy : x.1 = y.1 := by
      apply Subtype.ext
      simpa only [fullLogLatticeAssemble_apply, map_add, fullLogCentered_hyperplane,
        fullLogCentered_constant, add_zero] using hcenter
    exact Prod.ext hy hz
  · intro x
    obtain ⟨y, z, h⟩ := (mem_augmentedFullLogUnitLattice_iff E x).mp x.2
    exact ⟨(y, z), Subtype.ext h⟩

/-- The enlarged lattice is the direct product of its unit part and ordinary integers. -/
def fullLogIntegralSplit :
    augmentedFullLogUnitLattice E ≃ₗ[ℤ] (fullLogUnitLattice E × ℤ) :=
  (LinearEquiv.ofBijective (fullLogLatticeAssemble E)
    (fullLogLatticeAssemble_bijective E)).symm

@[simp] theorem fullLogIntegralSplit_symm_apply (x : fullLogUnitLattice E × ℤ) :
    ((fullLogIntegralSplit E).symm x : InfinitePlace E → ℝ) =
      (x.1 : fullLogHyperplane E) + fullLogConstant E (x.2 : ℝ) := rfl

@[simp] theorem fullLogIntegralSplit_fst (x : augmentedFullLogUnitLattice E) :
    ((fullLogIntegralSplit E x).1 : fullLogHyperplane E) = fullLogCentered E x := by
  obtain ⟨y, rfl⟩ := (fullLogIntegralSplit E).symm.surjective x
  simp

@[simp] theorem fullLogIntegralSplit_snd (x : augmentedFullLogUnitLattice E) :
    ((fullLogIntegralSplit E x).2 : ℝ) = fullLogMean E x := by
  obtain ⟨y, rfl⟩ := (fullLogIntegralSplit E).symm.surjective x
  simp

variable [Algebra F E]

/-- Restrict the arithmetic hyperplane action to the full logarithmic unit lattice. -/
def fullLogUnitLatticeAut : (E ≃ₐ[F] E) →*
    (fullLogUnitLattice E ≃ₗ[ℤ] fullLogUnitLattice E) where
  toFun g :=
    { toFun := fun x => ⟨fullLogHyperplaneAut F E g x,
        fullLogUnitLattice_invariant F E g x x.2⟩
      invFun := fun x => ⟨fullLogHyperplaneAut F E g⁻¹ x,
        fullLogUnitLattice_invariant F E g⁻¹ x x.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_zsmul _ _ _ }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem fullLogUnitLatticeAut_apply (g : E ≃ₐ[F] E) (x : fullLogUnitLattice E) :
    (fullLogUnitLatticeAut F E g x : fullLogHyperplane E) =
      fullLogHyperplaneAut F E g x := rfl

/-- Restrict the arithmetic full-coordinate action to the augmented lattice. -/
def augmentedFullLogUnitLatticeAut : (E ≃ₐ[F] E) →*
    (augmentedFullLogUnitLattice E ≃ₗ[ℤ] augmentedFullLogUnitLattice E) where
  toFun g :=
    { toFun := fun x => ⟨fullLogPermutation F E g x,
        augmentedFullLogUnitLattice_invariant E F g x x.2⟩
      invFun := fun x => ⟨fullLogPermutation F E g⁻¹ x,
        augmentedFullLogUnitLattice_invariant E F g⁻¹ x x.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_zsmul _ _ _ }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem augmentedFullLogUnitLatticeAut_apply (g : E ≃ₐ[F] E)
    (x : augmentedFullLogUnitLattice E) :
    (augmentedFullLogUnitLatticeAut F E g x : InfinitePlace E → ℝ) =
      fullLogPermutation F E g x := rfl

theorem fullLogLatticeAssemble_equivariant (g : E ≃ₐ[F] E) (x : fullLogUnitLattice E × ℤ) :
    fullLogLatticeAssemble E (fullLogUnitLatticeAut F E g x.1, x.2) =
      augmentedFullLogUnitLatticeAut F E g (fullLogLatticeAssemble E x) := by
  apply Subtype.ext
  simp

/-- The integral splitting intertwines the arithmetic action and the trivial integer action. -/
theorem fullLogIntegralSplit_equivariant (g : E ≃ₐ[F] E)
    (x : augmentedFullLogUnitLattice E) :
    fullLogIntegralSplit E (augmentedFullLogUnitLatticeAut F E g x) =
      (fullLogUnitLatticeAut F E g (fullLogIntegralSplit E x).1,
        (fullLogIntegralSplit E x).2) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [fullLogCentered_equivariant]
  · apply Int.cast_injective (α := ℝ)
    simp

end Langlands.ClassField.Global
