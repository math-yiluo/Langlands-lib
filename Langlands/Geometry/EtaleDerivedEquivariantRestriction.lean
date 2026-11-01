import Langlands.Geometry.EtaleDerivedActionRestriction
import Langlands.Geometry.EtaleDerivedEquivariantDiagram
import Langlands.Geometry.EtaleEquivariantCoefficientRestriction

/-! # Group restriction of actual derived equivariant diagrams -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t t' wS wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable [∀ i : J, HasDerivedCategory.{wS}
  (EtaleDerivedSections.ModuleSheaf (S.obj i).unop R)]
variable [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}
variable {H : Type t'} [Group H] (φ : H →* G)

namespace EquivariantCoefficientDiagram

/-- Derived action diagrams commute with restriction of the acting group. -/
def restrictGroupDerivedSectionsIso (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (restrictGroup φ D).derivedSections ≅
      D.derivedSections ⋙ Action.res (DerivedCategory.Plus (ModuleCat.{u} R)) φ :=
  NatIso.ofComponents
    (fun i => (restrictionDerivedSectionsFunctorIso R (ρ i) φ).app (D.obj i))
    (fun {i j} a => by
      apply Action.Hom.ext
      simp only [Iso.app_hom, Action.comp_hom, derivedSections_map_hom,
        restrictionDerivedSectionsFunctorIso_hom_app_hom, Functor.comp_map,
        Action.res_map_hom, restrictGroup_forget]
      change D.forget.derivedSections.map a ≫ 𝟙 _ =
        𝟙 _ ≫ D.forget.derivedSections.map a
      rw [Category.comp_id, Category.id_comp])

/-- The derived group-restriction comparison is natural in coefficient diagrams. -/
def restrictGroupDerivedSectionsFunctorIso :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ ⋙
        derivedSectionsFunctor ≅
      derivedSectionsFunctor ⋙
        (Functor.whiskeringRight J
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) H)).obj
          (Action.res (DerivedCategory.Plus (ModuleCat.{u} R)) φ) :=
  NatIso.ofComponents (fun D => restrictGroupDerivedSectionsIso φ D)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (restrictionDerivedSectionsFunctorIso R (ρ i) φ).hom.naturality (α.app i))

/-- The comparison has the identity underlying derived map at every vertex. -/
@[simp] theorem restrictGroupDerivedSectionsIso_hom_app_hom
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((restrictGroupDerivedSectionsIso φ D).hom.app i).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).obj (D.obj i).obj) :=
  rfl

/-- Group restriction commutes with canonical cohomology recovery as a diagram map. -/
theorem restrictGroup_derivedHomology (D : EquivariantCoefficientDiagram R S ρ hρ)
    (q : ℕ) :
    Functor.whiskerRight (restrictGroupDerivedSectionsIso φ D).hom
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction H) ≫
        Functor.whiskerRight (derivedSectionsHomologyIso D q).hom
          (Action.res (ModuleCat.{u} R) φ) =
      (derivedSectionsHomologyIso (restrictGroup φ D) q).hom ≫
        (restrictGroupCohomologyIso φ D q).hom := by
  apply NatTrans.ext
  funext i
  exact restriction_derivedHomology R (ρ i) φ (D.obj i) q

/-- Group restriction commutes with canonical degree-zero section recovery. -/
theorem restrictGroup_derivedZero (D : EquivariantCoefficientDiagram R S ρ hρ) :
    Functor.whiskerRight (restrictGroupDerivedSectionsIso φ D).hom
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction H) ≫
        Functor.whiskerRight (derivedSectionsZeroIso D).hom
          (Action.res (ModuleCat.{u} R) φ) =
      (derivedSectionsZeroIso (restrictGroup φ D)).hom ≫
        (restrictGroupSectionsIso φ D).hom := by
  apply NatTrans.ext
  funext i
  exact restriction_derivedZero R (ρ i) φ (D.obj i)

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
