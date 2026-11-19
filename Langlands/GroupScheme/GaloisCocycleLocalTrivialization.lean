import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.GaloisCocycleRefinement

/-! # Galois values of a trivialization over an extended base field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The point of the pullback cover induced by the two compatible coefficient inclusions. -/
def pullbackCoverPoint :
    cover K M ⟶ (Over.pullback (Spec.algebraMap F K)).obj (cover F L) :=
  ringPointBaseChangeEquiv F K M (cover F L) (coverMap F L M)

variable [Normal F L]

/-- A trivialization over the pullback to an extended base field gives a Galois coboundary
formula on any coefficient field containing the original coefficient field and the new base. -/
theorem exists_galois_coboundary_of_baseChange_isTrivial (ξ : Cocycle G (cover F L))
    (h : let b := Spec.algebraMap F K
      (ξ.baseChange b ((Over.pullback b).obj (cover F L))
        ((Over.mapPullbackAdj b).counit.app (cover F L))).IsTrivial) :
    ∃ a : G.affinePoints (CommAlgCat.of F M), ∀ σ : M ≃ₐ[K] M,
      GaloisPoint.relativeExtend F L M G (value ξ ((σ.restrictScalars F).restrictNormal L)) =
        a * (GaloisPoint.conjugate F M G (σ.restrictScalars F) a)⁻¹ := by
  let b := Spec.algebraMap F K
  let U := cover F L
  let V := (Over.pullback b).obj U
  let r := (Over.mapPullbackAdj b).counit.app U
  obtain ⟨f, hf⟩ := ξ.exists_of_baseChange_isTrivial b V r h
  let d := coverMap F L M
  let x : cover K M ⟶ V := pullbackCoverPoint (F := F) (L := L)
  let t : cover F M ⟶ (Over.map b).obj V :=
    (ringTestRestrictScalarsIso F K M).inv ≫ (Over.map b).map x
  have ht₁ : t ≫ r = d := by
    apply Over.OverMorphism.ext
    simp only [t, Over.comp_left, Over.map_map_left, ringTestRestrictScalarsIso_inv_left]
    exact ringPointBaseChangeEquiv_left_fst F K M U d
  have ht₂ : t.left ≫ V.hom = Spec.algebraMap K M := by
    simp only [t, Over.comp_left, Over.map_map_left, ringTestRestrictScalarsIso_inv_left]
    exact Over.w x
  refine ⟨t ≫ f, fun σ => ?_⟩
  let s := σ.restrictScalars F
  have hs : (arrow F M s ≫ t).left ≫ V.hom = t.left ≫ V.hom := by
    rw [Over.comp_left, Category.assoc, ht₂]
    change (arrow K M σ).left ≫ (cover K M).hom = (cover K M).hom
    exact Over.w (arrow K M σ)
  have hval := hf t (arrow F M s ≫ t) hs.symm
  rw [Category.assoc (arrow F M s) t r, ht₁, arrow_coverMap,
    Category.assoc (arrow F M s) t f] at hval
  change _ = (t ≫ f) * (GaloisPoint.conjugate F M G s (t ≫ f))⁻¹ at hval
  rw [← hval]
  change d ≫ ξ.toFun (𝟙 U) (arrow F L (s.restrictNormal L)) = _
  have hn := (ξ.naturality d (𝟙 U) (arrow F L (s.restrictNormal L))).symm
  rw [Category.comp_id d] at hn
  exact hn

end Langlands.GroupScheme.GaloisCocycle
