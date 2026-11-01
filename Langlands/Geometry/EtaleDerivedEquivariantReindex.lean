import Langlands.Geometry.EtaleDerivedEquivariantDiagram
import Langlands.Geometry.EtaleEquivariantCoefficientReindex

/-! # Reindexing actual equivariant derived-section diagrams -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t v' w' wS wT

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
variable {K : Type v'} [Category.{w'} K] (F : K ⥤ J)

local instance : ∀ i : K, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((F ⋙ S).obj i).unop R) :=
  fun i => inferInstanceAs
    (HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf (S.obj (F.obj i)).unop R))

namespace EquivariantCoefficientDiagram

/-- Actual derived action diagrams reindex by precomposition. -/
theorem reindex_derivedSections (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (reindex F D).derivedSections = F ⋙ D.derivedSections := rfl

/-- The canonical comparison for reindexing derived action diagrams. -/
def reindexDerivedSectionsIso (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (reindex F D).derivedSections ≅ F ⋙ D.derivedSections :=
  Iso.refl _

/-- Reindexing derived sections commutes naturally with coefficient morphisms. -/
def reindexDerivedSectionsFunctorIso :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙
        derivedSectionsFunctor ≅
      derivedSectionsFunctor ⋙
        (Functor.whiskeringLeft K J
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)).obj F :=
  NatIso.ofComponents (fun D => reindexDerivedSectionsIso F D)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The reindexing comparison retains the canonical cohomology comparison. -/
theorem reindex_derivedSectionsHomologyIso_hom_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (q : ℕ) (i : K) :
    (derivedSectionsHomologyIso (reindex F D) q).hom.app i =
      (derivedSectionsHomologyIso D q).hom.app (F.obj i) := rfl

/-- The inverse cohomology comparison also reindexes by its components. -/
theorem reindex_derivedSectionsHomologyIso_inv_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (q : ℕ) (i : K) :
    (derivedSectionsHomologyIso (reindex F D) q).inv.app i =
      (derivedSectionsHomologyIso D q).inv.app (F.obj i) := rfl

/-- Reindexing preserves the canonical comparison with ordinary sections. -/
theorem reindex_derivedSectionsZeroIso_hom_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : K) :
    (derivedSectionsZeroIso (reindex F D)).hom.app i =
      (derivedSectionsZeroIso D).hom.app (F.obj i) := rfl

/-- The inverse section comparison reindexes by its components. -/
theorem reindex_derivedSectionsZeroIso_inv_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : K) :
    (derivedSectionsZeroIso (reindex F D)).inv.app i =
      (derivedSectionsZeroIso D).inv.app (F.obj i) := rfl

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
