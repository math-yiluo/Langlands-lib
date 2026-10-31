import Langlands.Geometry.EtaleDerivedEquivariantMap
import Langlands.Geometry.EtaleEquivariantCoefficientDiagram

/-! # Equivariant derived sections over varying schemes -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t wS wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R]
variable {J : Type v} [Category.{w} J] (S : J ⥤ Scheme.{u}ᵒᵖ)
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable [∀ i : J, HasDerivedCategory.{wS}
  (EtaleDerivedSections.ModuleSheaf (S.obj i).unop R)]
variable [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {G : Type t} [Group G] (ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ)
variable (hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop)

namespace EquivariantCoefficientDiagram

variable {R S ρ hρ}

/-- Actual derived global sections with the geometric action at every vertex
and equivariant geometric transition maps. -/
def derivedSections (D : EquivariantCoefficientDiagram R S ρ hρ) :
    J ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G where
  obj i := (pullbackDerivedSectionsFunctor R (ρ i)).obj (D.obj i)
  map {i j} a :=
    (equivariantPullbackDerivedSections R (ρ i) (ρ j) (S.map a).unop (hρ a)).app
        (D.obj i) ≫
      (pullbackDerivedSectionsFunctor R (ρ j)).map (D.map a)
  map_id i := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, equivariantPullbackDerivedSections_app_hom,
      pullbackDerivedSectionsFunctor_map_hom, Action.id_hom]
    change D.forget.derivedSections.map (𝟙 i) = 𝟙 _
    exact D.forget.derivedSections.map_id i
  map_comp a b := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, equivariantPullbackDerivedSections_app_hom,
      pullbackDerivedSectionsFunctor_map_hom]
    change D.forget.derivedSections.map (a ≫ b) =
      D.forget.derivedSections.map a ≫ D.forget.derivedSections.map b
    exact D.forget.derivedSections.map_comp a b

/-- Forgetting the action gives the actual ordinary derived transition. -/
@[simp] theorem derivedSections_map_hom
    (D : EquivariantCoefficientDiagram R S ρ hρ) {i j : J} (a : i ⟶ j) :
    (D.derivedSections.map a).hom = D.forget.derivedSections.map a := by
  simp only [derivedSections, Action.comp_hom,
    equivariantPullbackDerivedSections_app_hom, pullbackDerivedSectionsFunctor_map_hom]
  rfl

/-- Compatible coefficient maps give natural equivariant derived maps. -/
def derivedSectionsMap {D E : EquivariantCoefficientDiagram R S ρ hρ}
    (α : D ⟶ E) : D.derivedSections ⟶ E.derivedSections where
  app i := (pullbackDerivedSectionsFunctor R (ρ i)).map (α.app i)
  naturality {i j} a := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, derivedSections_map_hom,
      pullbackDerivedSectionsFunctor_map_hom]
    change D.forget.derivedSections.map a ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj j).unop R).map
          ((α.app j).hom) =
      (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map
          ((α.app i).hom) ≫ E.forget.derivedSections.map a
    exact (CoefficientDiagram.derivedSectionsMap (forgetFunctor.map α)).naturality a

/-- Derived action diagrams are functorial in actual equivariant coefficients. -/
def derivedSectionsFunctor :
    EquivariantCoefficientDiagram R S ρ hρ ⥤
      (J ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G) where
  obj D := D.derivedSections
  map α := derivedSectionsMap α
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (pullbackDerivedSectionsFunctor R (ρ i)).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (pullbackDerivedSectionsFunctor R (ρ i)).map_comp (α.app i) (β.app i)

/-- Cohomology of the derived action diagram recovers the existing ordinary
equivariant cohomology diagram. -/
def derivedSectionsHomologyIso (D : EquivariantCoefficientDiagram R S ρ hρ)
    (q : ℕ) :
    D.derivedSections ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G ≅
      D.cohomology q :=
  NatIso.ofComponents
    (fun i => pullbackDerivedHomologyIso R (ρ i) (D.obj i) q)
    (fun {i j} a => by
      apply Action.Hom.ext
      change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
          (D.derivedSections.map a).hom ≫
          (EtaleDerivedSectionsPlus.homologyNatIso (S.obj j).unop R q).hom.app
            (D.obj j).obj =
        (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).hom.app
            (D.obj i).obj ≫ ((D.cohomology q).map a).hom
      rw [derivedSections_map_hom, cohomology_map_hom]
      exact (CoefficientDiagram.derivedSectionsHomologyIso D.forget q).hom.naturality a)

/-- Ordinary cohomology recovery is natural in equivariant coefficient diagrams. -/
def derivedSectionsHomologyFunctorIso (q : ℕ) :
    derivedSectionsFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) ⋙
        (Functor.whiskeringRight J (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G) ≅
      cohomologyFunctor q :=
  NatIso.ofComponents (fun D => derivedSectionsHomologyIso D q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (pullbackDerivedHomologyFunctorIso R (ρ i) q).hom.naturality (α.app i))

/-- Degree-zero derived cohomology recovers the ordinary section action diagram. -/
def derivedSectionsZeroIso (D : EquivariantCoefficientDiagram R S ρ hρ) :
    D.derivedSections ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
      D.sections :=
  derivedSectionsHomologyIso D 0 ≪≫ cohomologyZeroIso D

/-- Degree-zero section recovery is natural in equivariant coefficient diagrams. -/
def derivedSectionsZeroFunctorIso :
    derivedSectionsFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) ⋙
        (Functor.whiskeringRight J (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≅
      sectionsFunctor :=
  derivedSectionsHomologyFunctorIso 0 ≪≫ cohomologyZeroFunctorIso

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
