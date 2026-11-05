import Langlands.Geometry.Building.KPRelativeSplitNorm

/-! # Norm images in a tower of splitting fields -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

section Tower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [FiniteDimensional k L] [FiniteDimensional k M] [FiniteDimensional L M]
  [IsGalois k L] [IsGalois k M] [IsGalois L M]
  {ΓL ΓM : Type*} [LinearOrderedCommGroupWithZero ΓL]
  [LinearOrderedCommGroupWithZero ΓM]
  (vL : Valuation L ΓL) (vM : Valuation M ΓM) [vL.HasExtension vM]
  (hinv : ∀ (σ : M ≃ₐ[L] M) (z : M), vM (σ z) = vM z)
  (hunit : ∀ a : Lˣ, vL (a : L) = 1 →
    ∃ b : Mˣ, vM (b : M) = 1 ∧ Units.map (Algebra.norm L) b = a)
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  (hT : IsSplitTorus (baseChanged k L T.toGrp))

include hinv hunit hT in
/-- Enlarging a splitting field preserves the image of the bounded norm. -/
theorem torusNormIwahori_eq_of_tower :
    torusNormIwahori k M vM T = torusNormIwahori k L vL T := by
  apply le_antisymm
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := (mem_torusNormIwahori k M).mp ht
    let y := relativeBoundedRationalNorm k L M vL vM hinv T ⟨x, hx⟩
    refine (mem_torusNormIwahori k L).mpr ⟨y.val, y.property, ?_⟩
    exact rationalNorm_relativeRationalNorm k L M T x
  · intro t ht
    obtain ⟨x, hx, hxt⟩ := (mem_torusNormIwahori k L).mp ht
    obtain ⟨y, hy⟩ := relativeBoundedRationalNorm_surjective_of_split
      k L M vL vM hinv T hunit hT ⟨x, hx⟩
    have hval := congrArg Subtype.val hy
    change relativeRationalNorm k L M T y.val = x at hval
    refine (mem_torusNormIwahori k M).mpr ⟨y.val, y.property, ?_⟩
    rw [← rationalNorm_relativeRationalNorm k L M T y.val, hval, hxt]

/-- The identity of ambient points identifies the two bounded norm images. -/
def torusNormTowerEquiv :
    torusNormIwahori k M vM T ≃* torusNormIwahori k L vL T :=
  MulEquiv.subgroupCongr (torusNormIwahori_eq_of_tower k L M vL vM hinv hunit T hT)

@[simp] theorem torusNormTowerEquiv_coe (t : torusNormIwahori k M vM T) :
    (torusNormTowerEquiv k L M vL vM hinv hunit T hT t : rationalPoints T.toGrp) = t := rfl

end Tower

end Langlands.Geometry.Building
