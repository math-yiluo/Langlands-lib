import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsScalarTowerStatement
import Langlands.AlgebraicGeometry.Modules.SchemeIsoDerivedSectionsProof
import Langlands.Cohomology.PerfectModuleComplexBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Universal perfect representatives under a scalar tower: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

namespace DerivedSections

/-- Scheme-isomorphism transport with explicit equations for the structure
map and the map used to pull back the coefficient. -/
def relativeDerivedSectionsIsoOfComp
    {R : CommRingCat.{u}} {X Y Z : Scheme.{u}} (e : X ≅ Y)
    {f : X ⟶ Spec R} {g : Y ⟶ Spec R} (hf : e.hom ≫ g = f)
    {a : X ⟶ Z} {b : Y ⟶ Z} (ha : e.hom ≫ b = a) (M : Z.Modules) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pullback a).obj M) ≅
      (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pullback b).obj M) := by
  subst f
  subst a
  exact
    (DerivedPlus.derivedComplex (relativeGlobalSections (e.hom ≫ g)) ⋙
      DerivedCategory.Plus.ι).mapIso
        ((Scheme.Modules.pullbackComp e.hom b).app M).symm ≪≫
      (relativeDerivedSectionsPullbackIso e g).app
        ((Scheme.Modules.pullback b).obj M)

/-- Actual derived sections on the iterated affine base change identify with
those on the direct base change along the composite ring map. -/
def relativeDerivedSectionsScalarTowerIso
    {R S T : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (φ : R ⟶ S) (ψ : S ⟶ T) (M : X.Modules) :
    (DerivedPlus.derivedComplex
        (relativeGlobalSections
          (pullback.snd (pullback.snd f (Spec.map φ)) (Spec.map ψ))) ⋙
        DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd f (Spec.map φ)) (Spec.map ψ))).obj
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).obj M)) ≅
      (DerivedPlus.derivedComplex
        (relativeGlobalSections (pullback.snd f (Spec.map (φ ≫ ψ)))) ⋙
        DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (φ ≫ ψ)))).obj M) := by
  rw [Spec.map_comp]
  let e := pullbackLeftPullbackSndIso f (Spec.map φ) (Spec.map ψ)
  have hf : e.hom ≫ pullback.snd f (Spec.map ψ ≫ Spec.map φ) =
      pullback.snd (pullback.snd f (Spec.map φ)) (Spec.map ψ) := by
    exact pullbackLeftPullbackSndIso_hom_snd f (Spec.map φ) (Spec.map ψ)
  have ha : e.hom ≫ pullback.fst f (Spec.map ψ ≫ Spec.map φ) =
      pullback.fst (pullback.snd f (Spec.map φ)) (Spec.map ψ) ≫
        pullback.fst f (Spec.map φ) := by
    exact pullbackLeftPullbackSndIso_hom_fst f (Spec.map φ) (Spec.map ψ)
  exact
    (DerivedPlus.derivedComplex
      (relativeGlobalSections
        (pullback.snd (pullback.snd f (Spec.map φ)) (Spec.map ψ))) ⋙
      DerivedCategory.Plus.ι).mapIso
        ((Scheme.Modules.pullbackComp
          (pullback.fst (pullback.snd f (Spec.map φ)) (Spec.map ψ))
          (pullback.fst f (Spec.map φ))).app M) ≪≫
      relativeDerivedSectionsIsoOfComp e hf ha M

end DerivedSections

/-- The extended fixed complex represents all further actual scalar changes. -/
theorem universalPerfectSectionsScalarTower :
    UniversalPerfectSectionsScalarTowerStatement.{u} := by
  intro R X f M K hK S φ
  refine ⟨ModuleComplex.isStrictlyPerfect_baseChange φ.hom hK.1,
    hK.2.2 S φ, ?_⟩
  intro T ψ
  obtain ⟨α⟩ := hK.2.2 T (φ ≫ ψ)
  exact ⟨(DerivedCategory.Q.mapIso
      ((ModuleComplex.baseChangeCompIso φ.hom ψ.hom).app K)).symm ≪≫
    α ≪≫ (DerivedSections.relativeDerivedSectionsScalarTowerIso f φ ψ M).symm⟩

end Langlands.AlgebraicGeometry.Modules
