import Langlands.AlgebraicGeometry.Modules.PresheafPullbackFreeYoneda
import Langlands.AlgebraicGeometry.Modules.FreeYonedaTensor

/-! # Presheaf pullback tensor comparison on free Yoneda generators

The canonical presheaf pullback tensor comparison is the hom of an explicit
isomorphism when both inputs are free Yoneda module presheaves on opens.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

local instance (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

private abbrev freeOpen (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) :=
  (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V)

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (V W : Y.Opens)

private def tensorGeneratorPullbackIsoAux
    (eY : freeOpen Y (V ⊓ W) ≅ freeOpen Y V ⊗ freeOpen Y W)
    (eX : freeOpen X ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)) ≅
      freeOpen X ((TopologicalSpace.Opens.map f.base).obj V) ⊗
        freeOpen X ((TopologicalSpace.Opens.map f.base).obj W)) :
    (presheafPullback f).obj (freeOpen Y V ⊗ freeOpen Y W) ≅
      (presheafPullback f).obj (freeOpen Y V) ⊗
        (presheafPullback f).obj (freeOpen Y W) :=
  (presheafPullback f).mapIso eY.symm ≪≫
    presheafPullbackFreeYonedaIso f (V ⊓ W) ≪≫ eX ≪≫
      (tensorIso (presheafPullbackFreeYonedaIso f V)
        (presheafPullbackFreeYonedaIso f W)).symm

private lemma tensorGeneratorPullbackDiagram
    (eY : freeOpen Y (V ⊓ W) ≅ freeOpen Y V ⊗ freeOpen Y W)
    (eX : freeOpen X ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)) ≅
      freeOpen X ((TopologicalSpace.Opens.map f.base).obj V) ⊗
        freeOpen X ((TopologicalSpace.Opens.map f.base).obj W))
    (hY : eY.hom.app (op (V ⊓ W)) (ModuleCat.freeMk (𝟙 (V ⊓ W))) =
      ModuleCat.freeMk (homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
        ModuleCat.freeMk (homOfLE (inf_le_right : V ⊓ W ≤ W)))
    (hX : eX.hom.app (op ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)))
        (ModuleCat.freeMk (𝟙 ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)))) =
      ModuleCat.freeMk ((TopologicalSpace.Opens.map f.base).map
        (homOfLE (inf_le_left : V ⊓ W ≤ V))) ⊗ₜ
      ModuleCat.freeMk ((TopologicalSpace.Opens.map f.base).map
        (homOfLE (inf_le_right : V ⊓ W ≤ W)))) :
    (presheafPullback f).map eY.hom ≫
        presheafPullbackTensorComparisonApp f (freeOpen Y V) (freeOpen Y W) ≫
        (tensorIso (presheafPullbackFreeYonedaIso f V)
          (presheafPullbackFreeYonedaIso f W)).hom =
      (presheafPullbackFreeYonedaIso f (V ⊓ W)).hom ≫ eX.hom := by
  apply ((presheafPullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply PresheafOfModules.freeYonedaEquiv.injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_naturality_right]
  change ((tensorIso (presheafPullbackFreeYonedaIso f V)
      (presheafPullbackFreeYonedaIso f W)).hom.app
        (op ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W))))
      ((((presheafPullbackPushforwardAdjunction f).homEquiv _ _
        (presheafPullbackTensorComparisonApp f (freeOpen Y V) (freeOpen Y W))).app
          (op (V ⊓ W)))
        (eY.hom.app (op (V ⊓ W)) (ModuleCat.freeMk (𝟙 (V ⊓ W))))) =
    eX.hom.app _
      ((((presheafPullbackPushforwardAdjunction f).homEquiv _ _
        (presheafPullbackFreeYonedaIso f (V ⊓ W)).hom).app (op (V ⊓ W)))
          (ModuleCat.freeMk (𝟙 (V ⊓ W))))
  rw [hY, homEquiv_presheafPullbackTensorComparisonApp_app_tmul,
    presheafPullbackFreeYonedaIso_hom_unit]
  erw [hX]
  change ((presheafPullbackFreeYonedaIso f V).hom.app _ ⊗ₘ
    (presheafPullbackFreeYonedaIso f W).hom.app _) _ = _
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul
      (R := X.presheaf.obj (op ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)))),
    presheafPullbackFreeYonedaIso_hom_unit_app,
    presheafPullbackFreeYonedaIso_hom_unit_app]

private lemma tensorGeneratorPullbackIsoAux_hom
    (eY : freeOpen Y (V ⊓ W) ≅ freeOpen Y V ⊗ freeOpen Y W)
    (eX : freeOpen X ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)) ≅
      freeOpen X ((TopologicalSpace.Opens.map f.base).obj V) ⊗
        freeOpen X ((TopologicalSpace.Opens.map f.base).obj W))
    (hY : eY.hom.app (op (V ⊓ W)) (ModuleCat.freeMk (𝟙 (V ⊓ W))) =
      ModuleCat.freeMk (homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
        ModuleCat.freeMk (homOfLE (inf_le_right : V ⊓ W ≤ W)))
    (hX : eX.hom.app (op ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)))
        (ModuleCat.freeMk (𝟙 ((TopologicalSpace.Opens.map f.base).obj (V ⊓ W)))) =
      ModuleCat.freeMk ((TopologicalSpace.Opens.map f.base).map
        (homOfLE (inf_le_left : V ⊓ W ≤ V))) ⊗ₜ
      ModuleCat.freeMk ((TopologicalSpace.Opens.map f.base).map
        (homOfLE (inf_le_right : V ⊓ W ≤ W)))) :
    (tensorGeneratorPullbackIsoAux f V W eY eX).hom =
      presheafPullbackTensorComparisonApp f (freeOpen Y V) (freeOpen Y W) := by
  apply (cancel_epi ((presheafPullback f).map eY.hom)).mp
  apply (cancel_mono (tensorIso (presheafPullbackFreeYonedaIso f V)
    (presheafPullbackFreeYonedaIso f W)).hom).mp
  rw [Category.assoc, Category.assoc,
    tensorGeneratorPullbackDiagram f V W eY eX hY hX]
  simp [tensorGeneratorPullbackIsoAux]

/-- The pullback tensor comparison on a pair of free Yoneda module generators,
constructed through the generator at the intersection and its inverse image. -/
def presheafPullbackTensorComparisonFreeYonedaIso :
    (presheafPullback f).obj
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V) ⊗
          (PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj W)) ≅
      (presheafPullback f).obj
          ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)) ⊗
        (presheafPullback f).obj
          ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj W)) :=
  tensorGeneratorPullbackIsoAux f V W (freeYonedaInfTensorIso V W)
    (freeYonedaInfTensorIso ((TopologicalSpace.Opens.map f.base).obj V)
      ((TopologicalSpace.Opens.map f.base).obj W))

/-- The constructed isomorphism has exactly the canonical comparison as its hom. -/
@[simp]
lemma presheafPullbackTensorComparisonFreeYonedaIso_hom :
    (presheafPullbackTensorComparisonFreeYonedaIso f V W).hom =
      presheafPullbackTensorComparisonApp f
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj W)) := by
  apply tensorGeneratorPullbackIsoAux_hom
  · exact freeYonedaInfTensorIso_hom_app_id V W
  · have hleft :
        (TopologicalSpace.Opens.map f.base).map
            (homOfLE (inf_le_left : V ⊓ W ≤ V)) =
          homOfLE (inf_le_left :
            (TopologicalSpace.Opens.map f.base).obj V ⊓
                (TopologicalSpace.Opens.map f.base).obj W ≤
              (TopologicalSpace.Opens.map f.base).obj V) :=
      Subsingleton.elim _ _
    have hright :
        (TopologicalSpace.Opens.map f.base).map
            (homOfLE (inf_le_right : V ⊓ W ≤ W)) =
          homOfLE (inf_le_right :
            (TopologicalSpace.Opens.map f.base).obj V ⊓
                (TopologicalSpace.Opens.map f.base).obj W ≤
              (TopologicalSpace.Opens.map f.base).obj W) :=
      Subsingleton.elim _ _
    rw [hleft, hright]
    exact freeYonedaInfTensorIso_hom_app_id
      ((TopologicalSpace.Opens.map f.base).obj V)
      ((TopologicalSpace.Opens.map f.base).obj W)

end Langlands.Scheme.Modules
