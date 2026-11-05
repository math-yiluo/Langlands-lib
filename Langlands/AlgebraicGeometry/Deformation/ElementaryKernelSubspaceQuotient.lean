import Langlands.AlgebraicGeometry.Deformation.ArtinianElementaryKernel
import Langlands.AlgebraicGeometry.Deformation.ArtinianQuotients
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Quotienting an elementary Artinian test by a residue-kernel subspace -/

noncomputable section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianTest.ElementaryKernelSubspaceQuotient

open ElementaryKernel

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {A B : ArtinianTest k K} (q : A ⟶ B) [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out

local instance : Module K (Kernel q) := residueModule q hq

/-- The image of a residue-field kernel subspace is an actual ideal of the source ring. -/
def subspaceIdeal (W : Submodule K (Kernel q)) : Ideal A.algebra where
  carrier := {a | ∃ x : Kernel q, x ∈ W ∧ x.val = a}
  zero_mem' := ⟨0, W.zero_mem, rfl⟩
  add_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, W.add_mem hx hy, rfl⟩
  smul_mem' := by
    rintro a b ⟨x, hx, rfl⟩
    refine ⟨a • x, ?_, rfl⟩
    rw [← augmentation_smul q hq a x]
    exact W.smul_mem _ hx

@[simp]
lemma mem_subspaceIdeal (W : Submodule K (Kernel q)) (x : Kernel q) :
    x.val ∈ subspaceIdeal q W ↔ x ∈ W := by
  constructor
  · rintro ⟨y, hy, he⟩
    have h : y = x := Subtype.ext he
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma subspaceIdeal_le_kernel (W : Submodule K (Kernel q)) :
    subspaceIdeal q W ≤ RingHom.ker (toAlgHom q).toRingHom := by
  rintro a ⟨x, hx, rfl⟩
  exact x.property

lemma subspaceIdeal_le_augmentation (W : Submodule K (Kernel q)) :
    subspaceIdeal q W ≤ RingHom.ker A.augmentation.toRingHom := by
  rw [ker_augmentation]
  exact (subspaceIdeal_le_kernel q W).trans (ker_le_maximalIdeal q)

lemma maximalIdeal_mul_subspaceIdeal (W : Submodule K (Kernel q)) :
    IsLocalRing.maximalIdeal A.algebra * subspaceIdeal q W = ⊥ := by
  exact le_antisymm
    ((mul_le_mul' le_rfl (subspaceIdeal_le_kernel q W)).trans_eq hq.2) bot_le

/-- The actual quotient test with the descended original residue augmentation. -/
def test (W : Submodule K (Kernel q)) : ArtinianTest k K :=
  quotient A (subspaceIdeal q W) (subspaceIdeal_le_augmentation q W)

/-- The original source projects to the actual subspace quotient test. -/
def projection (W : Submodule K (Kernel q)) : A ⟶ test q W :=
  quotientMap A (subspaceIdeal q W) (subspaceIdeal_le_augmentation q W)

/-- The elementary arrow descends to the actual quotient source. -/
def reduction (W : Submodule K (Kernel q)) : test q W ⟶ B :=
  quotientLift q (subspaceIdeal q W) (subspaceIdeal_le_augmentation q W)
    (subspaceIdeal_le_kernel q W)

lemma projection_reduction (W : Submodule K (Kernel q)) :
    projection q W ≫ reduction q W = q :=
  quotientMap_lift q _ _ _

lemma projection_elementary (W : Submodule K (Kernel q)) :
    IsElementarySurjection (projection q W) := by
  refine ⟨quotientMap_surjective _ _ _, ?_⟩
  change IsLocalRing.maximalIdeal A.algebra *
    RingHom.ker (toAlgHom (quotientMap A _ _)).toRingHom = ⊥
  rw [ker_quotientMap]
  exact maximalIdeal_mul_subspaceIdeal q W

lemma ker_reduction (W : Submodule K (Kernel q)) :
    RingHom.ker (toAlgHom (reduction q W)).toRingHom =
      (RingHom.ker (toAlgHom q).toRingHom).map
        (Ideal.Quotient.mk (subspaceIdeal q W)) := by
  change RingHom.ker (Ideal.Quotient.lift _ (toAlgHom q).toRingHom _) = _
  exact Ideal.ker_quotient_lift _ _

lemma reduction_elementary (W : Submodule K (Kernel q)) :
    IsElementarySurjection (reduction q W) := by
  refine ⟨quotientLift_surjective _ _ _ _ hq.1, ?_⟩
  rw [ker_reduction]
  have : IsLocalRing (A.algebra ⧸ subspaceIdeal q W) :=
    inferInstanceAs (IsLocalRing (test q W).algebra)
  change IsLocalRing.maximalIdeal (A.algebra ⧸ subspaceIdeal q W) *
    (RingHom.ker (toAlgHom q).toRingHom).map
      (Ideal.Quotient.mk (subspaceIdeal q W)) = ⊥
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (subspaceIdeal q W)) Ideal.Quotient.mk_surjective,
    ← Ideal.map_mul, hq.2, Ideal.map_bot]

/-- The actual map on the elementary kernels is induced by the ordinary quotient. -/
def kernelMap (W : Submodule K (Kernel q)) : Kernel q →+ Kernel (reduction q W) where
  toFun x := ⟨Ideal.Quotient.mk (subspaceIdeal q W) x.val, x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

@[simp]
lemma kernelMap_val (W : Submodule K (Kernel q)) (x : Kernel q) :
    (kernelMap q W x).val = Ideal.Quotient.mk (subspaceIdeal q W) x.val := rfl

lemma kernelMap_surjective (W : Submodule K (Kernel q)) :
    Function.Surjective (kernelMap q W) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y.val
  have hqa : a ∈ RingHom.ker (toAlgHom q).toRingHom := by
    change toAlgHom (reduction q W) (Ideal.Quotient.mk (subspaceIdeal q W) a) = 0
    rw [ha]
    exact y.property
  exact ⟨⟨a, hqa⟩, Subtype.ext ha⟩

local instance (W : Submodule K (Kernel q)) : Module K (Kernel (reduction q W)) :=
  residueModule (reduction q W) (reduction_elementary q W)

/-- The actual quotient kernel map is linear for the canonically descended residue actions. -/
def kernelLinearMap (W : Submodule K (Kernel q)) :
    Kernel q →ₗ[K] Kernel (reduction q W) where
  __ := kernelMap q W
  map_smul' := by
    intro c x
    obtain ⟨a, rfl⟩ := A.augmentation_surjective c
    change kernelMap q W (A.augmentation a • x) =
      A.augmentation a • kernelMap q W x
    rw [augmentation_smul q hq a x]
    have he : A.augmentation a =
        (test q W).augmentation (toAlgHom (projection q W) a) := rfl
    rw [he, augmentation_smul (reduction q W) (reduction_elementary q W)]
    apply Subtype.ext
    exact map_mul _ _ _

lemma ker_kernelLinearMap (W : Submodule K (Kernel q)) :
    LinearMap.ker (kernelLinearMap q W) = W := by
  ext x
  change kernelMap q W x = 0 ↔ x ∈ W
  rw [Subtype.ext_iff]
  change Ideal.Quotient.mk (subspaceIdeal q W) x.val = 0 ↔ x ∈ W
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_subspaceIdeal]

/-- The actual new kernel is the quotient of the original residue-field kernel by the chosen subspace. -/
def quotientKernelEquiv (W : Submodule K (Kernel q)) :
    ((Kernel q) ⧸ W) ≃ₗ[K] Kernel (reduction q W) :=
  (Submodule.quotEquivOfEq W _ (ker_kernelLinearMap q W).symm).trans
    ((kernelLinearMap q W).quotKerEquivOfSurjective (kernelMap_surjective q W))

@[simp]
lemma quotientKernelEquiv_mk (W : Submodule K (Kernel q)) (x : Kernel q) :
    quotientKernelEquiv q W (Submodule.Quotient.mk x) = kernelMap q W x := by
  simp [quotientKernelEquiv]
  rfl

end Langlands.AlgebraicGeometry.Deformation.ArtinianTest.ElementaryKernelSubspaceQuotient
