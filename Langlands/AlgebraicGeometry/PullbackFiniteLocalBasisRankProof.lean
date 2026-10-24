import Langlands.AlgebraicGeometry.FiniteLocalBasisStatements
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Pullback preserves finite local bases and specified rank -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

private def localPullback (U : Y.Opens) :
    SheafOfModules (Y.ringCatSheaf.over U) ⥤
      SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor ⋙
    AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U) ⋙
      (AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse

private def localPullbackUnit (U : Y.Opens) :
    SheafOfModules.unit (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      (localPullback f U).obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) :=
  ((AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
    ((AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso
      (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf) ≪≫ pullbackUnitIso (f ∣_ U)) ≪≫
    (f ⁻¹ᵁ U).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm

set_option maxHeartbeats 800000 in
private def localPullbackIso (U : Y.Opens) (M : Y.Modules) :
    (localPullback f U).obj (M.over U) ≅
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
    ((AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M) ≪≫
      (Langlands.AlgebraicGeometry.Picard.restrictPullbackIso f U M).symm ≪≫
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).symm) ≪≫
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).unitIso.app
      (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U))).symm

private def pullbackGenerators {M : Y.Modules} (U : Y.Opens)
    (G : (M.over U).GeneratingSections) :
    (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over
      (f ⁻¹ᵁ U)).GeneratingSections :=
  let F := localPullback f U
  have : PreservesColimitsOfSize.{u, u} F := by
    dsimp [F, localPullback]
    infer_instance
  (G.map F (localPullbackUnit f U)).ofEpi (localPullbackIso f U M).hom

private lemma pullbackGenerators_isIso {M : Y.Modules} (U : Y.Opens)
    (G : (M.over U).GeneratingSections) [IsIso G.π] :
    IsIso (pullbackGenerators f U G).π := by
  have : PreservesColimitsOfSize.{u, u} (localPullback f U) := by
    dsimp [localPullback]
    infer_instance
  dsimp [pullbackGenerators]
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

private def pullbackLocalData {M : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M) :
    SheafOfModules.LocalGeneratorsData.{u}
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := by
    rw [_root_.Opens.coversTop_iff, IsOpenCover]
    have h := q.coversTop
    rw [_root_.Opens.coversTop_iff, IsOpenCover] at h
    change (⨆ i, (TopologicalSpace.Opens.map f.base).obj (q.X i)) = ⊤
    exact (TopologicalSpace.Opens.map_iSup f.base q.X).symm.trans
      ((congrArg (TopologicalSpace.Opens.map f.base).obj h).trans rfl)
  generators i := pullbackGenerators f (q.X i) (q.generators i)

set_option maxRecDepth 2048 in
private lemma pullbackLocalData_free {M : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData] :
    (pullbackLocalData f q).IsLocallyFreeData where
  isIso i := pullbackGenerators_isIso f (q.X i) (q.generators i)

/-- Actual module pullback preserves finite local bases and every specified finite rank. -/
theorem pullbackFiniteLocalBasisRank : PullbackFiniteLocalBasisRankStatement.{u} := by
  intro X Y f M
  constructor
  · rintro ⟨q, hfree, hfinite⟩
    let := hfree
    refine ⟨pullbackLocalData f q, pullbackLocalData_free f q, ?_⟩
    refine { isFiniteType := fun i ↦ ?_ }
    exact ⟨(hfinite.isFiniteType i).finite⟩
  · intro n hn
    obtain ⟨q, hfree, hrank⟩ := hn
    let := hfree
    exact ⟨pullbackLocalData f q, pullbackLocalData_free f q, hrank⟩

end Langlands.Scheme.Modules
