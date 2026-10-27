import Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensorStatement
import Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensorFreeYoneda

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Limits MonoidalCategory

namespace Langlands.Scheme.Modules

private lemma isIso_app_of_freeYoneda
    {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {D : Type w} [Category.{v} D]
    {F G : PresheafOfModules.{u} R ⥤ D}
    [PreservesColimitsOfSize.{u, u} F] [PreservesColimitsOfSize.{u, u} G]
    (α : F ⟶ G)
    (h : ∀ V : C, IsIso (α.app ((PresheafOfModules.free R).obj (yoneda.obj V))))
    (M : PresheafOfModules.{u} R) : IsIso (α.app M) := by
  have hcoprod (N : PresheafOfModules.{u} R) :
      IsIso (α.app N.freeYonedaCoproduct) := by
    let K := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := N))
    have (j : Discrete N.Elements) : IsIso ((Functor.whiskerLeft K α).app j) := h j.as.1.unop
    have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K α (colimit.cocone K)
      (colimit.isColimit K)
  have : PreservesColimitsOfSize.{0, 0} F := preservesSmallestColimits_of_preservesColimits F
  have : PreservesColimitsOfSize.{0, 0} G := preservesSmallestColimits_of_preservesColimits G
  let K := parallelPair M.toFreeYonedaCoproduct 0
  have (j : WalkingParallelPair) : IsIso ((Functor.whiskerLeft K α).app j) := by
    cases j
    · exact hcoprod _
    · exact hcoprod _
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α
    M.freeYonedaCoproductsCokernelCofork M.isColimitFreeYonedaCoproductsCokernelCofork

local instance presheafPullbackTensorProofMonoidalCategory
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

private lemma comparison_isIso_of_freeYoneda
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ V W : Y.Opens, IsIso (presheafPullbackTensorComparisonApp f
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj W)))) :
    IsIso (presheafPullbackTensorComparison f) := by
  let L := presheafPullback f
  have : L.IsLeftAdjoint := (presheafPullbackPushforwardAdjunction f).isLeftAdjoint
  have : PreservesColimitsOfSize.{u, u} L := inferInstance
  have (M : Y.PresheafOfModules) : PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (tensorLeft (show PresheafOfModulesOfCommRing.{u} Y.presheaf from M)))
  have (N : Y.PresheafOfModules) : PreservesColimitsOfSize.{u, u} (tensorRight N) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (tensorRight (show PresheafOfModulesOfCommRing.{u} Y.presheaf from N)))
  have (M : X.PresheafOfModules) : PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (tensorLeft (show PresheafOfModulesOfCommRing.{u} X.presheaf from M)))
  have (N : X.PresheafOfModules) : PreservesColimitsOfSize.{u, u} (tensorRight N) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (tensorRight (show PresheafOfModulesOfCommRing.{u} X.presheaf from N)))
  have hleft (V : Y.Opens) (N : Y.PresheafOfModules) :
      IsIso (presheafPullbackTensorComparisonApp f
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)) N) := by
    let M := (PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)
    let α : tensorLeft M ⋙ L ⟶ L ⋙ tensorLeft (L.obj M) :=
      { app := fun N ↦ presheafPullbackTensorComparisonApp f M N
        naturality := fun N N' b ↦ by
          simpa using presheafPullbackTensorComparisonApp_naturality f (𝟙 M) b }
    exact isIso_app_of_freeYoneda α (h V) N
  have hboth (M N : Y.PresheafOfModules) :
      IsIso (presheafPullbackTensorComparisonApp f M N) := by
    let α : tensorRight N ⋙ L ⟶ L ⋙ tensorRight (L.obj N) :=
      { app := fun M ↦ presheafPullbackTensorComparisonApp f M N
        naturality := fun M M' a ↦ by
          simpa using presheafPullbackTensorComparisonApp_naturality f a (𝟙 N) }
    exact isIso_app_of_freeYoneda α (fun V ↦ hleft V N) M
  have (MN : Y.PresheafOfModules × Y.PresheafOfModules) :
      IsIso ((presheafPullbackTensorComparison f).app MN) := hboth MN.1 MN.2
  exact NatIso.isIso_of_isIso_app _

/-- The fixed canonical presheaf pullback tensor comparison is invertible. -/
theorem presheafPullbackTensorComparisonIsIso :
    presheafPullbackTensorComparisonIsIsoStatement.{u} := by
  intro X Y f
  apply comparison_isIso_of_freeYoneda f
  intro V W
  rw [← presheafPullbackTensorComparisonFreeYonedaIso_hom f V W]
  infer_instance

end Langlands.Scheme.Modules
