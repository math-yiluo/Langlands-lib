import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChangeZero
import Langlands.AlgebraicGeometry.SectionPullback

/-! # Naturality and composition of ordinary sections base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Square

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The ordinary sections maps form a natural transformation in the coefficient sheaf. -/
def sectionsBaseChangeNatTrans :
    relativeGlobalSections f ⟶
      Scheme.Modules.pullback g ⋙ relativeGlobalSections f' ⋙
        ModuleCat.restrictScalars φ.hom where
  app M := sectionsBaseChangeMap φ f f' g w M
  naturality := by
    intro M N a
    exact sectionsBaseChangeMap_naturality φ f f' g w a

/-- The scalar-linear sections maps form a natural transformation. -/
def scalarSectionsBaseChangeNatTrans :
    relativeGlobalSections f ⋙ ModuleCat.extendScalars φ.hom ⟶
      Scheme.Modules.pullback g ⋙ relativeGlobalSections f' where
  app M := scalarSectionsBaseChangeMap φ f f' g w M
  naturality := by
    intro M N a
    exact scalarSectionsBaseChangeMap_naturality φ f f' g w a

/-- The ordinary map is the published actual section pullback on the top open. -/
lemma sectionsBaseChangeMap_eq_sectionPullback (M : X.Modules)
    (x : (relativeGlobalSections f).obj M) :
    sectionsBaseChangeMap φ f f' g w M x =
      Langlands.Scheme.Modules.sectionPullback g M ⊤ x := rfl

/-- Restriction of an ordinary base-change image is the pullback of the restricted section. -/
lemma sectionsBaseChangeMap_restrict (M : X.Modules) (U : X.Opens)
    (x : (relativeGlobalSections f).obj M) :
    ((Scheme.Modules.pullback g).obj M).presheaf.map
        ((TopologicalSpace.Opens.map g.base).map (homOfLE le_top : U ⟶ ⊤)).op
        (sectionsBaseChangeMap φ f f' g w M x) =
      Langlands.Scheme.Modules.sectionPullback g M U
        (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op x) :=
  (Langlands.Scheme.Modules.sectionPullback_restrict g M
    (homOfLE le_top : U ⟶ ⊤) x).symm

end Square

section Composition

variable {X X' X'' : Scheme.{u}} {R R' R'' : CommRingCat.{u}}
  (φ : R ⟶ R') (ψ : R' ⟶ R'')
  (f : X ⟶ Spec R) (f' : X' ⟶ Spec R') (f'' : X'' ⟶ Spec R'')
  (g : X' ⟶ X) (g' : X'' ⟶ X')
  (w : g ≫ f = f' ≫ Spec.map φ) (w' : g' ≫ f' = f'' ≫ Spec.map ψ)

include w w' in
/-- Two commuting base-change squares compose. -/
lemma sectionsBaseChangeSquare_comp :
    (g' ≫ g) ≫ f = f'' ≫ Spec.map (φ ≫ ψ) := by
  rw [Category.assoc, w, ← Category.assoc g' f', w', Category.assoc,
    ← Spec.map_comp]

/-- Ordinary sections base change composes under the canonical scalar-restriction
and sheaf-pullback composition comparisons. -/
@[reassoc]
theorem sectionsBaseChangeMap_comp (M : X.Modules) :
    sectionsBaseChangeMap φ f f' g w M ≫
        (ModuleCat.restrictScalars φ.hom).map
          (sectionsBaseChangeMap ψ f' f'' g' w' ((Scheme.Modules.pullback g).obj M)) ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv.app _ ≫
        (ModuleCat.restrictScalars (φ ≫ ψ).hom).map
          ((relativeGlobalSections f'').map ((Scheme.Modules.pullbackComp g' g).hom.app M)) =
      sectionsBaseChangeMap (φ ≫ ψ) f f'' (g' ≫ g)
        (sectionsBaseChangeSquare_comp φ ψ f f' f'' g g' w w') M := by
  ext x
  exact Langlands.Scheme.Modules.sectionPullback_comp g' g M ⊤ x

/-- Scalar-linear sections base change composes under the canonical
scalar-extension and sheaf-pullback composition comparisons. -/
@[reassoc]
theorem scalarSectionsBaseChangeMap_comp (M : X.Modules) :
    (ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app
        ((relativeGlobalSections f).obj M) ≫
        (ModuleCat.extendScalars ψ.hom).map
          (scalarSectionsBaseChangeMap φ f f' g w M) ≫
        scalarSectionsBaseChangeMap ψ f' f'' g' w' ((Scheme.Modules.pullback g).obj M) ≫
        (relativeGlobalSections f'').map ((Scheme.Modules.pullbackComp g' g).hom.app M) =
      scalarSectionsBaseChangeMap (φ ≫ ψ) f f'' (g' ≫ g)
        (sectionsBaseChangeSquare_comp φ ψ f f' f'' g g' w w') M := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ConcreteCategory.comp_apply, ModuleCat.extendScalarsComp_hom_app_one_tmul]
  have hφ := scalarSectionsBaseChangeMap_one_tmul φ f f' g w M x
  have hψ := scalarSectionsBaseChangeMap_one_tmul ψ f' f'' g' w'
    ((Scheme.Modules.pullback g).obj M)
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ x)
  have hcomp := scalarSectionsBaseChangeMap_one_tmul (φ ≫ ψ) f f'' (g' ≫ g)
    (sectionsBaseChangeSquare_comp φ ψ f f' f'' g g' w w') M x
  change (relativeGlobalSections f'').map ((Scheme.Modules.pullbackComp g' g).hom.app M)
      (scalarSectionsBaseChangeMap ψ f' f'' g' w' ((Scheme.Modules.pullback g).obj M)
        ((1 : R'') ⊗ₜ[R',ψ.hom]
          (scalarSectionsBaseChangeMap φ f f' g w M ((1 : R') ⊗ₜ[R,φ.hom] x)))) =
    scalarSectionsBaseChangeMap (φ ≫ ψ) f f'' (g' ≫ g)
      (sectionsBaseChangeSquare_comp φ ψ f f' f'' g g' w w') M
      ((1 : R'') ⊗ₜ[R,(φ ≫ ψ).hom] x)
  rw [hφ, hψ, hcomp]
  exact Langlands.Scheme.Modules.sectionPullback_comp g' g M ⊤ x

end Composition

section Identity

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- The identity base-change square commutes. -/
lemma sectionsBaseChangeSquare_id :
    (𝟙 X) ≫ f = f ≫ Spec.map (𝟙 R) := by simp

/-- Ordinary sections base change along the identity recovers the original section. -/
theorem sectionsBaseChangeMap_id (M : X.Modules) :
    sectionsBaseChangeMap (𝟙 R) f f (𝟙 X) (sectionsBaseChangeSquare_id f) M ≫
        (ModuleCat.restrictScalarsId R).hom.app _ ≫
        (relativeGlobalSections f).map ((Scheme.Modules.pullbackId X).hom.app M) =
      𝟙 ((relativeGlobalSections f).obj M) := by
  ext x
  exact Langlands.Scheme.Modules.sectionPullback_id M ⊤ x

/-- Scalar-linear sections base change along the identity is the canonical
identity scalar-extension comparison followed by inverse identity pullback. -/
theorem scalarSectionsBaseChangeMap_id (M : X.Modules) :
    scalarSectionsBaseChangeMap (𝟙 R) f f (𝟙 X) (sectionsBaseChangeSquare_id f) M ≫
        (relativeGlobalSections f).map ((Scheme.Modules.pullbackId X).hom.app M) =
      (ModuleCat.extendScalarsId R).hom.app ((relativeGlobalSections f).obj M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ConcreteCategory.comp_apply, scalarSectionsBaseChangeMap_one_tmul]
  erw [ModuleCat.extendScalarsId_hom_app_one_tmul]
  exact Langlands.Scheme.Modules.sectionPullback_id M ⊤ x

end Identity

end Langlands.AlgebraicGeometry.Modules.DerivedSections
