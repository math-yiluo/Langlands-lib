import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.GaloisCocycleLocalTrivialization
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.BaseChangeReflection

/-! # Galois cocycle coefficients after a change of base field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

set_option backward.isDefEq.respectTransparency false

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M]
  {G H : GroupScheme (Spec (CommRingCat.of F))}

local notation "b" => Spec.algebraMap F K
local notation "P" => (Over.map (Spec.algebraMap F K))
local notation "i" => ringTestRestrictScalarsIso F K M

/-- The base-changed cocycle restricted to the chosen compatible field cover. -/
def scalarExtension (ξ : Cocycle G (cover F L)) :
    Cocycle ((GroupScheme.baseChange (b)).obj G) (cover K M) :=
  (ξ.baseChangePullback (b)).refine pullbackCoverPoint

/-- The pullback adjunction identifies the new group points with the original group points
on the same coefficient field. -/
def scalarExtensionPointsEquiv (G : GroupScheme (Spec (CommRingCat.of F))) :
    ((cover K M) ⟶ ((GroupScheme.baseChange (b)).obj G).X) ≃*
      G.affinePoints (CommAlgCat.of F M) where
  toFun x := (i).inv ≫ baseChangePointsEquiv (b) G (cover K M) x
  invFun x := (baseChangePointsEquiv (b) G (cover K M)).symm ((i).hom ≫ x)
  left_inv x := by simp only [Iso.hom_inv_id_assoc, MulEquiv.symm_apply_apply]
  right_inv x := by simp only [MulEquiv.apply_symm_apply, Iso.inv_hom_id_assoc]
  map_mul' x y := by rw [map_mul, MonObj.comp_mul]

private theorem scalarExtensionPointsEquiv_left (G : GroupScheme (Spec (CommRingCat.of F)))
    (x : cover K M ⟶ ((GroupScheme.baseChange (b)).obj G).X) :
    (scalarExtensionPointsEquiv G x).left = x.left ≫ pullback.fst G.X.hom (b) := by
  change ((i).inv ≫ baseChangePointsEquiv (b) G (cover K M) x).left = _
  simp only [Over.comp_left, ringTestRestrictScalarsIso_inv_left, Category.id_comp,
    baseChangePointsEquiv_left]

/-- The point comparison is natural in homomorphisms of coefficient groups. -/
theorem scalarExtensionPointsEquiv_comp (q : G ⟶ H)
    (x : cover K M ⟶ ((GroupScheme.baseChange (b)).obj G).X) :
    scalarExtensionPointsEquiv H (x ≫ ((GroupScheme.baseChange (b)).map q).hom.hom) =
      scalarExtensionPointsEquiv G x ≫ q.hom.hom := by
  change (i).inv ≫ baseChangePointsEquiv (b) H (cover K M)
      (x ≫ ((GroupScheme.baseChange (b)).map q).hom.hom) =
    ((i).inv ≫ baseChangePointsEquiv (b) G (cover K M) x) ≫ q.hom.hom
  simpa only [Category.assoc] using congrArg (fun z => (i).inv ≫ z)
    (baseChangePointsEquiv_comp (b) q (cover K M) x)

/-- The point comparison intertwines Galois actions by restriction of scalars. -/
theorem scalarExtensionPointsEquiv_conjugate
    (x : cover K M ⟶ ((GroupScheme.baseChange (b)).obj G).X) (σ : M ≃ₐ[K] M) :
    scalarExtensionPointsEquiv G (GaloisPoint.conjugate K M _ σ x) =
      GaloisPoint.relativeConjugate F K M G σ (scalarExtensionPointsEquiv G x) := by
  apply Over.OverMorphism.ext
  change (scalarExtensionPointsEquiv G (arrow K M σ ≫ x)).left =
    (arrow F M (σ.restrictScalars F) ≫ scalarExtensionPointsEquiv G x).left
  simp only [scalarExtensionPointsEquiv_left, Over.comp_left, Category.assoc]
  rfl

private theorem coverProjection_comp :
    (i).inv ≫ (P).map (pullbackCoverPoint (F := F) (K := K) (L := L) (M := M)) ≫
      (Over.mapPullbackAdj (b)).counit.app (cover F L) = coverMap F L M := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.map_map_left, ringTestRestrictScalarsIso_inv_left, Category.id_comp]
  exact ringPointBaseChangeEquiv_left_fst F K M (cover F L) (coverMap F L M)

/-- The crossed coefficients after a base change are the transported restrictions of the
original coefficients to the Galois group of the chosen local cover. -/
theorem value_scalarExtension [Normal F L] (ξ : Cocycle G (cover F L)) (σ : M ≃ₐ[K] M) :
    scalarExtensionPointsEquiv G (value (scalarExtension (K := K) (M := M) ξ) σ) =
      GaloisPoint.relativeExtend F L M G (value ξ ((σ.restrictScalars F).restrictNormal L)) := by
  let x := pullbackCoverPoint (F := F) (K := K) (L := L) (M := M)
  let r := (Over.mapPullbackAdj (b)).counit.app (cover F L)
  have h₁ : (i).inv ≫ (P).map x ≫ r = coverMap F L M := coverProjection_comp
  have hm : (i).inv ≫ (P).map (arrow K M σ) = arrow F M (σ.restrictScalars F) ≫ (i).inv := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.map_map_left, ringTestRestrictScalarsIso_inv_left,
      Category.id_comp]
    rfl
  have h₂ : (i).inv ≫ (P).map (arrow K M σ ≫ x) ≫ r =
      coverMap F L M ≫ arrow F L ((σ.restrictScalars F).restrictNormal L) := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((i).inv), hm]
    simp only [Category.assoc, h₁, arrow_coverMap]
  change (i).inv ≫ baseChangePointsEquiv (b) G (cover K M)
    ((ξ.baseChange (b) _ r).toFun (𝟙 _ ≫ x) (arrow K M σ ≫ x)) = _
  rw [Category.id_comp, Cocycle.baseChange_toFun, ← ξ.naturality]
  simp only [h₁, h₂]
  change _ = coverMap F L M ≫ ξ.toFun (𝟙 _)
    (arrow F L ((σ.restrictScalars F).restrictNormal L))
  simpa only [Category.comp_id] using ξ.naturality (coverMap F L M) (𝟙 _)
    (arrow F L ((σ.restrictScalars F).restrictNormal L))

/-- Triviality on the chosen field cover reflects triviality on the entire base-changed cover. -/
theorem isTrivial_baseChange_of_scalarExtension (ξ : Cocycle G (cover F L))
    (h : (scalarExtension (K := K) (M := M) ξ).IsTrivial) :
    (ξ.baseChangePullback (b)).IsTrivial := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc K M
  let : Surjective (cover K M).hom := hs
  let : Flat (cover K M).hom := hf
  let : QuasiCompact (cover K M).hom := hq
  exact Cocycle.IsTrivial.of_refine_fpqcCover _ h

end Langlands.GroupScheme.GaloisCocycle
