import Langlands.AlgebraicGeometry.Modules.PushforwardUnitIso
import Langlands.AlgebraicGeometry.Picard.MumfordBundle

/-! # Structure-module comparisons for abelian-scheme families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The structure module of the base is the direct image of that of an
abelian scheme, through the actual canonical comparison. -/
def pushforwardUnitIso :
    SheafOfModules.unit S.ringCatSheaf ≅
      (Scheme.Modules.pushforward A.X.hom).obj
        (SheafOfModules.unit A.X.left.ringCatSheaf) :=
  Langlands.Scheme.Modules.pushforwardUnitIso A.X.hom

@[simp]
lemma pushforwardUnitIso_hom :
    (pushforwardUnitIso A).hom =
      Langlands.Scheme.Modules.unitToPushforwardUnit A.X.hom := rfl

/-- The same comparison for every actual parameter-first base change
`T ×_S A → T`. -/
def relativePushforwardUnitIso (T : Over S) :
    SheafOfModules.unit T.left.ringCatSheaf ≅
      (Scheme.Modules.pushforward ((relativeProjection A.X.hom).app T)).obj
        (SheafOfModules.unit ((relativeSpace A.X.hom).obj T).ringCatSheaf) :=
  Langlands.Scheme.Modules.pushforwardUnitIso (pullback.fst T.hom A.X.hom)

@[simp]
lemma relativePushforwardUnitIso_hom (T : Over S) :
    (relativePushforwardUnitIso A T).hom =
      Langlands.Scheme.Modules.unitToPushforwardUnit
        ((relativeProjection A.X.hom).app T) := rfl

private lemma mumfordProduct_geometry :
    Smooth (mumfordProduct A).hom ∧ IsProper (mumfordProduct A).hom ∧
      GeometricallyConnected (mumfordProduct A).hom := by
  change Smooth (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) ∧
    IsProper (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) ∧
    GeometricallyConnected (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  exact ⟨inferInstance, inferInstance, GeometricallyConnected.comp _ _⟩

/-- The comparison for the target's exact self-product over the original base. -/
def mumfordPushforwardUnitIso :
    SheafOfModules.unit S.ringCatSheaf ≅
      (Scheme.Modules.pushforward (mumfordProduct A).hom).obj
        (SheafOfModules.unit (mumfordProduct A).left.ringCatSheaf) := by
  letI := (mumfordProduct_geometry A).1
  letI := (mumfordProduct_geometry A).2.1
  letI := (mumfordProduct_geometry A).2.2
  exact Langlands.Scheme.Modules.pushforwardUnitIso (mumfordProduct A).hom

@[simp]
lemma mumfordPushforwardUnitIso_hom :
    (mumfordPushforwardUnitIso A).hom =
      Langlands.Scheme.Modules.unitToPushforwardUnit (mumfordProduct A).hom := rfl

/-- The comparison for every actual base change of the self-product. -/
def mumfordRelativePushforwardUnitIso (T : Over S) :
    SheafOfModules.unit T.left.ringCatSheaf ≅
      (Scheme.Modules.pushforward
        ((relativeProjection (mumfordProduct A).hom).app T)).obj
        (SheafOfModules.unit
          ((relativeSpace (mumfordProduct A).hom).obj T).ringCatSheaf) := by
  letI := (mumfordProduct_geometry A).1
  letI := (mumfordProduct_geometry A).2.1
  letI := (mumfordProduct_geometry A).2.2
  exact Langlands.Scheme.Modules.pushforwardUnitIso
    (pullback.fst T.hom (mumfordProduct A).hom)

@[simp]
lemma mumfordRelativePushforwardUnitIso_hom (T : Over S) :
    (mumfordRelativePushforwardUnitIso A T).hom =
      Langlands.Scheme.Modules.unitToPushforwardUnit
        ((relativeProjection (mumfordProduct A).hom).app T) := rfl

end Langlands.AbelianScheme
