import Langlands.Geometry.Building.IntegerValuationBuildingData
import Mathlib.GroupTheory.Index

/-! # Finite permutation actions and intersections of one-stabilizers -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- Restrict the original rational-point action to an invariant finite subset
of the original reduced building. -/
def finiteSetPermutationHom
    (H : Subgroup (rationalPoints G)) (Y : Finset B.ReducedBuilding)
    (hY : ∀ h : H, ∀ y ∈ Y, (h : rationalPoints G) • y ∈ Y) :
    H →* Equiv.Perm (Y : Set B.ReducedBuilding) where
  toFun h :=
    { toFun := fun y => ⟨(h : rationalPoints G) • y, hY h y y.property⟩
      invFun := fun y => ⟨((h⁻¹ : H) : rationalPoints G) • y, hY h⁻¹ y y.property⟩
      left_inv := fun y =>
        Subtype.ext (inv_smul_smul (h : rationalPoints G) (y : B.ReducedBuilding))
      right_inv := fun y =>
        Subtype.ext (smul_inv_smul (h : rationalPoints G) (y : B.ReducedBuilding)) }
  map_one' := by
    ext y
    exact one_smul (rationalPoints G) (y : B.ReducedBuilding)
  map_mul' h j := by
    ext y
    exact mul_smul (h : rationalPoints G) (j : rationalPoints G) (y : B.ReducedBuilding)

@[simp] theorem finiteSetPermutationHom_apply
    (H : Subgroup (rationalPoints G)) (Y : Finset B.ReducedBuilding)
    (hY : ∀ h : H, ∀ y ∈ Y, (h : rationalPoints G) • y ∈ Y)
    (h : H) (y : (Y : Set B.ReducedBuilding)) :
    ((B.finiteSetPermutationHom H Y hY h y : (Y : Set B.ReducedBuilding)) :
      B.ReducedBuilding) = (h : rationalPoints G) • (y : B.ReducedBuilding) :=
  rfl

/-- Nonempty intersections of one-stabilizers are the common character kernel
intersected with the original pointwise fixer of the finite set. -/
theorem iInf_oneStabilizer_eq
    (Y : Finset B.ReducedBuilding) (hY : Y.Nonempty) :
    (⨅ y ∈ Y, B.oneStabilizer y) =
      characterValuationKernel v G ⊓ B.pointwiseFixer (Y : Set B.ReducedBuilding) := by
  ext h
  simp only [Subgroup.mem_iInf, B.mem_oneStabilizer, Subgroup.mem_inf,
    B.apartment.mem_pointwiseFixer, Finset.mem_coe]
  constructor
  · intro hh
    obtain ⟨y, hy⟩ := hY
    exact ⟨(hh y hy).1, fun z hz => (hh z hz).2⟩
  · rintro ⟨hh, hfix⟩ y hy
    exact ⟨hh, hfix y hy⟩

/-- Inside a subgroup of the character kernel, fixing every point of an
invariant finite set is precisely the kernel of its actual permutation action. -/
theorem finiteSetPermutationHom_ker
    (H : Subgroup (rationalPoints G)) (Y : Finset B.ReducedBuilding)
    (hH : H ≤ characterValuationKernel v G)
    (hY : ∀ h : H, ∀ y ∈ Y, (h : rationalPoints G) • y ∈ Y) :
    (B.finiteSetPermutationHom H Y hY).ker =
      (⨅ y ∈ Y, B.oneStabilizer y).subgroupOf H := by
  ext h
  constructor
  · intro hh
    change (h : rationalPoints G) ∈ ⨅ y ∈ Y, B.oneStabilizer y
    simp only [Subgroup.mem_iInf]
    intro y hy
    apply B.mem_oneStabilizer.mpr
    refine ⟨hH h.property, ?_⟩
    exact congrArg Subtype.val (Equiv.congr_fun hh ⟨y, hy⟩)
  · intro hh
    change B.finiteSetPermutationHom H Y hY h = 1
    ext y
    change (h : rationalPoints G) • (y : B.ReducedBuilding) = y
    have hm : (h : rationalPoints G) ∈ B.oneStabilizer y :=
      (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh y)) y.property
    exact (B.mem_oneStabilizer.mp hm).2

/-- The one-stabilizer intersection of an invariant finite set is normal and
has finite index inside every subgroup of the character kernel preserving it.
Containment of the intersection in that subgroup is a separate assertion. -/
theorem normal_finiteIndex_iInf_oneStabilizer
    (H : Subgroup (rationalPoints G)) (Y : Finset B.ReducedBuilding)
    (hH : H ≤ characterValuationKernel v G)
    (hY : ∀ h : H, ∀ y ∈ Y, (h : rationalPoints G) • y ∈ Y) :
    ((⨅ y ∈ Y, B.oneStabilizer y).subgroupOf H).Normal ∧
      ((⨅ y ∈ Y, B.oneStabilizer y).subgroupOf H).FiniteIndex := by
  classical
  rw [← B.finiteSetPermutationHom_ker H Y hH hY]
  exact ⟨inferInstance, inferInstance⟩

end Langlands.Geometry.Building.IntegerValuationBuildingData
