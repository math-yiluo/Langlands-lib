import Langlands.Global.InfiniteAdelicTangentComplexification
import Langlands.Global.InfiniteAdelicLeviEnveloping
import Langlands.GroupScheme.Lie.CocharacterGrading

/-! # Cocharacter eigenspaces of the archimedean tangent Lie algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme
open Langlands.Algebra.BaseChangeEigenvectors
open scoped Langlands.GroupScheme.Lie.FieldLie

variable (F : Type u) [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "LieF" => Additive (lieKernel G F)
local notation "TangentG" =>
  GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)

/-- The real span of the archimedean realizations of a subspace of `Lie G` over `F`. -/
def realizedTangentSubmodule (W : Submodule F LieF) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Submodule ℝ (smoothModel F d) :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  Submodule.span ℝ (tangentVector F G hG '' (W : Set LieF))

theorem realizedTangentSubmodule_iSup {I : Type*} (W : I → Submodule F LieF) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    realizedTangentSubmodule F hG (⨆ i, W i) = ⨆ i, realizedTangentSubmodule F hG (W i) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.iSup_induction W
      (motive := fun y => tangentVector F G hG y ∈ ⨆ i, realizedTangentSubmodule F hG (W i))
      hx ?_ ?_ ?_
    · exact fun i y hy => Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨y, hy, rfl⟩)
    ·
      have heq := tangentVector_ratCast_smul F G hG 0 (0 : LieF)
      rw [Rat.cast_zero, Rat.cast_zero, zero_smul, zero_smul] at heq
      rw [heq]
      exact Submodule.zero_mem _
    · intro y z hy hz
      rw [tangentVector_add]
      exact Submodule.add_mem _ hy hz
  · refine iSup_le fun i => Submodule.span_mono ?_
    exact Set.image_mono fun _ hx => Submodule.mem_iSup_of_mem i hx

theorem realizedTangentSubmodule_top :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    realizedTangentSubmodule F hG ⊤ = ⊤ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  rw [realizedTangentSubmodule, Submodule.top_coe, Set.image_univ, span_range_tangentVector]

section Range

variable {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {e : ℕ} (hH : SmoothOfRelativeDimension e H.X.hom)

/-- The real span of the realizations of the algebraic differential's image is the image
of the real tangent map. -/
theorem realizedTangentSubmodule_range (j : H ⟶ G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F H hH
    letI := smoothChartedSpace F G hG
    realizedTangentSubmodule F hG (LinearMap.range (Lie.targetMapLinear j F)) =
      LinearMap.range (pointTangent F hH hG j).toLinearMap := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F H hH
  let := smoothChartedSpace F G hG
  let D := (pointTangent F hH hG j).toLinearMap
  have hD (x : Additive (lieKernel H F)) :
      D (tangentVector F H hH x) = tangentVector F G hG (Lie.targetMapLinear j F x) :=
    tangentVector_naturality F hH hG j x
  have h := Submodule.map_span D (Set.range (tangentVector F H hH))
  rw [span_range_tangentVector, Submodule.map_top] at h
  change _ = LinearMap.range D
  rw [realizedTangentSubmodule, LinearMap.coe_range, ← Set.range_comp, h,
    ← Set.range_comp]
  simp only [Function.comp_def, hD]

end Range

section Grading

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The realization of the cocharacter tangent `dχ(1)` at infinity. -/
def cocharacterTangentVector : smoothModel F d :=
  tangentVector F G hG (Lie.cocharacterLieVector χ)

/-- The integral eigenspaces of the real adjoint action are real spans of the rational
cocharacter weight spaces. -/
theorem eigenspace_ad_cocharacterTangentVector (n : ℤ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothLieGroup F G hG
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    (LieAlgebra.ad ℝ TangentG (cocharacterTangentVector F hG χ)).eigenspace (n : ℝ) =
      realizedTangentSubmodule F hG (weightSpace χ (Gm.powerHom _ n)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let T := LieAlgebra.ad ℝ TangentG (cocharacterTangentVector F hG χ)
  let W (m : ℤ) := realizedTangentSubmodule F hG (weightSpace χ (Gm.powerHom _ m))
  have htop : ⨆ m, W m = ⊤ := by
    simp only [W, ← realizedTangentSubmodule_iSup]
    exact (congrArg (realizedTangentSubmodule F hG) (Lie.iSup_weightSpace_powerHom_eq_top χ)).trans
      (realizedTangentSubmodule_top F hG)
  have heigen (m : ℤ) (x : TangentG) (hx : x ∈ W m) : T x = (m : ℝ) • x := by
    apply Module.End.mem_eigenspace_iff.mp
    refine Submodule.span_le.mpr ?_ hx
    rintro _ ⟨y, hy, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅(show TangentG from tangentVector F G hG (Lie.cocharacterLieVector χ)),
      (show TangentG from tangentVector F G hG y)⁆ =
      (m : ℝ) • (show TangentG from tangentVector F G hG y)
    rw [← tangentVector_lie, Lie.lie_cocharacterLieVector_of_mem_weightSpace χ m hy]
    simpa only [Rat.cast_intCast] using tangentVector_ratCast_smul F G hG (m : ℚ) y
  exact (eq_eigenspace_of_iSup_eq_top T W (fun m : ℤ => (m : ℝ)) Int.cast_injective
    heigen htop n).symm

end Grading

end Langlands.Global.InfiniteAdelicGroupPoints
