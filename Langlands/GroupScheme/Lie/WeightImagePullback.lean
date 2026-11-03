import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Lie.Intersection

/-! # Weight witnesses through a monomorphic subgroup and its intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}
  {T : CommGroupScheme (Spec R)}
  {P M G : GroupScheme (Spec R)}
  [IsAffineHom M.X.hom] [IsAffineHom G.X.hom]

/-- The actual differential restricted to a character weight space. -/
def weightSpaceMap (s : M ⟶ G) (t : T.toGrp ⟶ M) (χ : characterLattice T) :
    weightSpace t χ →ₗ[R] weightSpace (t ≫ s) χ where
  toFun X := ⟨targetMapLinear s R X,
    lieKernelHomLinear_mem_weightSpace s t χ X.property⟩
  map_add' X Y := Subtype.ext (map_add (targetMapLinear s R)
    (X : Additive (lieKernel M R)) (Y : Additive (lieKernel M R)))
  map_smul' c X := Subtype.ext (map_smul (targetMapLinear s R) c
    (X : Additive (lieKernel M R)))

@[simp] theorem weightSpaceMap_coe (s : M ⟶ G) (t : T.toGrp ⟶ M)
    (χ : characterLattice T) (X : weightSpace t χ) :
    (weightSpaceMap s t χ X : Additive (lieKernel G R)) =
      targetMapLinear s R X := rfl

/-- A monomorphic embedding gives an injective map on every character weight space. -/
theorem weightSpaceMap_injective (s : M ⟶ G) [Mono s.hom.hom]
    (t : T.toGrp ⟶ M) (χ : characterLattice T) :
    Function.Injective (weightSpaceMap s t χ) := by
  intro X Y h
  apply Subtype.ext
  apply targetMapLinear_injective s R
  exact congrArg (fun Z : weightSpace (t ≫ s) χ =>
    (Z : Additive (lieKernel G R))) h

/-- The exact nonzero weight/Lie-image witness is preserved and reflected
when the ambient group is enlarged by a monomorphic homomorphism. -/
theorem weightSpace_lieImage_comp_iff (s : M ⟶ G) [Mono s.hom.hom]
    (t : T.toGrp ⟶ M) (i : P ⟶ M) (χ : characterLattice T) :
    (∃ X : Additive (lieKernel G R),
      X ∈ weightSpace (t ≫ s) χ ∧ X ≠ 0 ∧
        ∃ Y : lieKernel P R, Y.val ≫ (i ≫ s).hom.hom = X.toMul.val) ↔
    (∃ X : Additive (lieKernel M R),
      X ∈ weightSpace t χ ∧ X ≠ 0 ∧
        ∃ Y : lieKernel P R, Y.val ≫ i.hom.hom = X.toMul.val) := by
  constructor
  · rintro ⟨X, hX, hX0, Y, hY⟩
    let Z : Additive (lieKernel M R) := Additive.ofMul (targetMap i R Y)
    have hZ : targetMapLinear s R Z = X := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa only [Z, lieKernelTargetLinear_toMul, toMul_ofMul, lieKernelTarget_val,
        Grp.comp_hom_hom, Category.assoc] using hY
    refine ⟨Z, ?_, ?_, Y, rfl⟩
    · apply (lieKernelHomLinear_mem_weightSpace_iff s t χ Z).mp
      rw [hZ]
      exact hX
    · intro h0
      apply hX0
      rw [← hZ, h0, map_zero]
  · rintro ⟨X, hX, hX0, Y, hY⟩
    refine ⟨weightSpaceMap s t χ ⟨X, hX⟩,
      (weightSpaceMap s t χ ⟨X, hX⟩).property, ?_, Y, ?_⟩
    · intro h0
      apply hX0
      apply targetMapLinear_injective s R
      simpa only [weightSpaceMap_coe, map_zero] using h0
    · simpa only [weightSpaceMap_coe, lieKernelTargetLinear_val,
        Grp.comp_hom_hom, ← Category.assoc] using
        congrArg (fun x => x ≫ s.hom.hom) hY

/-- An ambient nonzero weight vector lying in both subgroup Lie-images is
equivalent to a nonzero intrinsic weight vector of the monomorphic factor
lying in the Lie-image of the scheme-theoretic intersection. -/
theorem weightSpace_lieImage_subgroupIntersection_iff
    (j : P ⟶ G) (s : M ⟶ G) [Mono s.hom.hom]
    (t : T.toGrp ⟶ M) (χ : characterLattice T) :
    (∃ X : Additive (lieKernel G R),
      X ∈ weightSpace (t ≫ s) χ ∧ X ≠ 0 ∧
        (∃ Y : lieKernel P R, Y.val ≫ j.hom.hom = X.toMul.val) ∧
        (∃ Y : lieKernel M R, Y.val ≫ s.hom.hom = X.toMul.val)) ↔
    (∃ X : Additive (lieKernel M R),
      X ∈ weightSpace t χ ∧ X ≠ 0 ∧
        ∃ Y : lieKernel (subgroupIntersection j s) R,
          Y.val ≫ (subgroupIntersectionSnd j s).hom.hom = X.toMul.val) := by
  have hcomp :
      subgroupIntersectionHom j s = subgroupIntersectionSnd j s ≫ s :=
    subgroupIntersection_condition j s
  rw [← weightSpace_lieImage_comp_iff s t (subgroupIntersectionSnd j s) χ]
  rw [← hcomp]
  constructor
  · rintro ⟨X, hX, hX0, hP, hM⟩
    exact ⟨X, hX, hX0, (lieImage_subgroupIntersection_iff j s R X.toMul).mpr
      ⟨hP, hM⟩⟩
  · rintro ⟨X, hX, hX0, hI⟩
    obtain ⟨hP, hM⟩ := (lieImage_subgroupIntersection_iff j s R X.toMul).mp hI
    exact ⟨X, hX, hX0, hP, hM⟩

end Langlands.GroupScheme.Lie
