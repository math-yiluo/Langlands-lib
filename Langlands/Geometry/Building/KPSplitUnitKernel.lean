import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Torus.Lattice

/-! # Character-valuation kernels of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable (k : Type u) [Field k]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)

/-- On the multiplicative group, boundedness is exactly unit valuation. -/
theorem mem_gm_characterValuationKernel
    (x : rationalPoints (Gm (Spec (CommRingCat.of k))).toGrp) :
    x ∈ characterValuationKernel v (Gm (Spec (CommRingCat.of k))).toGrp ↔
      v (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k))) x : k) = 1 := by
  constructor
  · intro hx
    exact (mem_characterValuationKernel.mp hx) (Additive.ofMul (𝟙 _))
  · intro hx
    rw [mem_characterValuationKernel]
    intro χ
    let φ : Gm (Spec (CommRingCat.of k)) ⟶ Gm (Spec (CommRingCat.of k)) := χ
    change v (Gm.affinePointsEquiv (𝟙 _) (x ≫
      (CommGroupScheme.groupHom φ).hom.hom) : k) = 1
    have hφ : φ = (gmEndEquiv k).symm (gmEndEquiv k φ) :=
      ((gmEndEquiv k).symm_apply_apply φ).symm
    rw [hφ, gmEndEquiv_symm_comp, map_zpow, Units.val_zpow_eq_zpow_val, map_zpow₀, hx, one_zpow]

variable (I : Type u) [Fintype I]

/-- Coordinate cocharacters reconstruct every point of a split torus. -/
theorem splitPoint_decomposition
    (x : rationalPoints (splitTorus (Spec (CommRingCat.of k)) I)) :
    x = ∏ i, rationalPoints.map
      (CommGroupScheme.groupHom (splitTorus.single (Spec (CommRingCat.of k)) I i))
      (rationalPoints.map
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i)) x) := by
  have h := comp_groupHom_sum x Finset.univ
    (fun i => splitTorus.proj (Spec (CommRingCat.of k)) I i ≫
      splitTorus.single (Spec (CommRingCat.of k)) I i)
  rw [splitTorus.sum_proj_comp_single] at h
  have hid :
      (CommGroupScheme.groupHom
        (𝟙 (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))).hom.hom =
          𝟙 (splitTorus (Spec (CommRingCat.of k)) I).X := rfl
  rw [hid, Category.comp_id] at h
  refine h.trans (Finset.prod_congr rfl fun i _ => ?_)
  exact comp_groupHom_comp x (splitTorus.proj (Spec (CommRingCat.of k)) I i)
    (splitTorus.single (Spec (CommRingCat.of k)) I i)

/-- The bounded subgroup of a split torus is the product of its bounded
multiplicative-group coordinate subgroups. -/
def splitCharacterKernelEquiv :
    characterValuationKernel v (splitTorus (Spec (CommRingCat.of k)) I) ≃*
      (I → characterValuationKernel v (Gm (Spec (CommRingCat.of k))).toGrp) where
  toFun x i := ⟨rationalPoints.map
    (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i)) x,
    map_characterValuationKernel_le v
      (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i))
      ⟨x.val, x.property, rfl⟩⟩
  invFun y := by
    let z := (piPointsEquiv (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm (fun i => (y i).val)
    refine ⟨z, ?_⟩
    rw [splitPoint_decomposition k I z]
    apply Subgroup.prod_mem
    intro i _
    have hz : rationalPoints.map
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i)) z =
          (y i).val := piPointsEquiv_symm_π _ _ _ i
    rw [hz]
    exact map_characterValuationKernel_le v
      (CommGroupScheme.groupHom (splitTorus.single (Spec (CommRingCat.of k)) I i))
      ⟨(y i).val, (y i).property, rfl⟩
  left_inv x := Subtype.ext
    ((piPointsEquiv (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm_apply_apply x.val)
  right_inv y := by
    funext i
    apply Subtype.ext
    exact piPointsEquiv_symm_π
      (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp)
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (fun j => (y j).val) i
  map_mul' x y := by
    funext i
    exact Subtype.ext
      ((rationalPoints.map
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i))).map_mul
        x.val y.val)

@[simp] theorem splitCharacterKernelEquiv_apply
    (x : characterValuationKernel v (splitTorus (Spec (CommRingCat.of k)) I)) (i : I) :
    (splitCharacterKernelEquiv k v I x i : rationalPoints
      (Gm (Spec (CommRingCat.of k))).toGrp) =
        rationalPoints.map
          (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i)) x := rfl

end Langlands.Geometry.Building
