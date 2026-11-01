import Langlands.Geometry.EtaleDerivedEquivariantDiagram
import Langlands.Geometry.EtaleEquivariantFixedDiagram

/-! # Fixed-scheme specialization of actual equivariant derived diagrams -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t wS wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X R)]
variable [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {G : Type t} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)
variable (J : Type v) [Category.{w} J]

local instance : ∀ i : J, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((fixedSchemeDiagram X J).obj i).unop R) :=
  fun _ => inferInstanceAs (HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X R))

namespace EquivariantCoefficientDiagram

/-- Fixed-scheme derived transitions are the original coefficient maps under
the equivariant derived-section functor. -/
theorem ofFixed_derivedSections_map (D : J ⥤ EquivariantSheaf R ρ)
    {i j : J} (a : i ⟶ j) :
    (ofFixed R ρ J D).derivedSections.map a =
      (pullbackDerivedSectionsFunctor R ρ).map (D.map a) := by
  dsimp only [derivedSections, ofFixed, fixedSchemeDiagram, Functor.const]
  rw [(pullbackDerivedSectionsFunctor R ρ).map_comp, ← Category.assoc]
  erw [equivariantPullbackDerivedSections_id R ρ (D.obj i), Category.id_comp]

/-- Derived sections of fixed-scheme equivariant coefficients are
postcomposition by actual equivariant derived sections. -/
def ofFixedDerivedSectionsIso (D : J ⥤ EquivariantSheaf R ρ) :
    (ofFixed R ρ J D).derivedSections ≅ D ⋙ pullbackDerivedSectionsFunctor R ρ :=
  NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} a => by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.comp_map]
      using ofFixed_derivedSections_map R ρ J D a)

/-- The fixed-scheme comparison is natural in the full coefficient diagram. -/
def ofFixedDerivedSectionsFunctorIso :
    ofFixedFunctor R ρ J ⋙ derivedSectionsFunctor ≅
      (Functor.whiskeringRight J (EquivariantSheaf R ρ)
        (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)).obj
          (pullbackDerivedSectionsFunctor R ρ) :=
  NatIso.ofComponents (fun D => ofFixedDerivedSectionsIso R ρ J D)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The fixed-scheme comparison has the identity component at every vertex. -/
@[simp] theorem ofFixedDerivedSectionsIso_hom_app
    (D : J ⥤ EquivariantSheaf R ρ) (i : J) :
    (ofFixedDerivedSectionsIso R ρ J D).hom.app i =
      𝟙 ((pullbackDerivedSectionsFunctor R ρ).obj (D.obj i)) := rfl

/-- The fixed-scheme comparison commutes with canonical ordinary-cohomology recovery. -/
theorem ofFixed_derivedHomology (D : J ⥤ EquivariantSheaf R ρ) (q : ℕ) :
    Functor.whiskerRight (ofFixedDerivedSectionsIso R ρ J D).hom
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G) ≫
        Functor.whiskerLeft D (pullbackDerivedHomologyFunctorIso R ρ q).hom =
      (derivedSectionsHomologyIso (ofFixed R ρ J D) q).hom ≫
        (ofFixedCohomologyIso R ρ J D q).hom := by
  apply NatTrans.ext
  funext i
  change ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G).map
      (𝟙 _) ≫ (pullbackDerivedHomologyFunctorIso R ρ q).hom.app (D.obj i) =
    (pullbackDerivedHomologyFunctorIso R ρ q).hom.app (D.obj i) ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The fixed-scheme comparison commutes with canonical ordinary-section recovery. -/
theorem ofFixed_derivedZero (D : J ⥤ EquivariantSheaf R ρ) :
    Functor.whiskerRight (ofFixedDerivedSectionsIso R ρ J D).hom
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≫
        Functor.whiskerLeft D (pullbackDerivedZeroFunctorIso R ρ).hom =
      (derivedSectionsZeroIso (ofFixed R ρ J D)).hom ≫
        (ofFixedSectionsIso R ρ J D).hom := by
  apply NatTrans.ext
  funext i
  change ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G).map
      (𝟙 _) ≫ (pullbackDerivedZeroFunctorIso R ρ).hom.app (D.obj i) =
    (pullbackDerivedZeroFunctorIso R ρ).hom.app (D.obj i) ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
