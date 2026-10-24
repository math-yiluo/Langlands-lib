import Langlands.Geometry.EtaleEquivariantCoefficientReindex
import Langlands.Geometry.EtalePullbackGroupRestriction

/-!
# Group restriction of equivariant coefficient diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t t' t'' v' w'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}
variable {H : Type t'} [Group H] (φ : H →* G)

namespace EquivariantCoefficientDiagram

/-- Restrict every coefficient action and transition along one group homomorphism. -/
def restrictGroup (D : EquivariantCoefficientDiagram R S ρ hρ) :
    EquivariantCoefficientDiagram R S (fun i => (ρ i).comp φ)
      (fun a h => hρ a (φ h)) where
  obj i := (restrictionFunctor R (ρ i) φ).obj (D.obj i)
  map {i j} a := (restrictionFunctor R (ρ j) φ).map (D.map a)
  map_id i := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [restrictionFunctor_map_hom, equivariantDiagramRestrictionId_hom_app_hom,
      restrictionFunctor_obj_obj, forget] using D.forget.map_id i
  map_comp a b := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [TranslationAction.Equivariant.comp_hom, restrictionFunctor_map_hom,
      equivariantDiagramRestrictionComp_hom_app_hom, restrictionFunctor_obj_obj,
      equivariantPullback_map_hom, forget] using D.forget.map_comp a b

/-- Restriction retains the entire ordinary coefficient diagram. -/
@[simp] theorem restrictGroup_forget (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (restrictGroup φ D).forget = D.forget := rfl

/-- Restrict a coefficient morphism at every vertex. -/
def restrictGroupMap {D E : EquivariantCoefficientDiagram R S ρ hρ} (α : D ⟶ E) :
    restrictGroup φ D ⟶ restrictGroup φ E where
  app i := (restrictionFunctor R (ρ i) φ).map (α.app i)
  comm a := by
    apply TranslationAction.Equivariant.Hom.ext
    have h := congrArg TranslationAction.Equivariant.Hom.hom (α.comm a)
    exact h

/-- Group restriction is a functor on compatible equivariant coefficients. -/
def restrictGroupFunctor :
    EquivariantCoefficientDiagram R S ρ hρ ⥤
      EquivariantCoefficientDiagram R S (fun i => (ρ i).comp φ)
        (fun a h => hρ a (φ h)) where
  obj := restrictGroup φ
  map := restrictGroupMap φ
  map_id D := by
    apply Hom.ext
    funext i
    exact (restrictionFunctor R (ρ i) φ).map_id (D.obj i)
  map_comp α β := by
    apply Hom.ext
    funext i
    exact (restrictionFunctor R (ρ i) φ).map_comp (α.app i) (β.app i)

instance : (restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ).Faithful where
  map_injective h := by
    apply Hom.ext
    funext i
    apply (restrictionFunctor R (ρ i) φ).map_injective
    exact congrArg (fun α => α.app i) h

/-- Forgetting all actions commutes with group restriction. -/
def restrictGroupForgetFunctorIso :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ forgetFunctor ≅
      forgetFunctor :=
  Iso.refl _

/-- Evaluation after diagram restriction is restriction after evaluation. -/
def restrictGroupEvaluationIso (i : J) :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ evaluation i ≅
      evaluation i ⋙ restrictionFunctor R (ρ i) φ :=
  Iso.refl _

/-- The cohomology action diagram of restricted coefficients is the restricted diagram. -/
def restrictGroupCohomologyIso (D : EquivariantCoefficientDiagram R S ρ hρ) (q : ℕ) :
    (restrictGroup φ D).cohomology q ≅ D.cohomology q ⋙ Action.res (ModuleCat.{u} R) φ :=
  NatIso.ofComponents
    (fun i => (restrictionCohomologyFunctorIso R (ρ i) φ q).app (D.obj i))
    (fun {i j} a => by
      apply Action.Hom.ext
      simp only [Iso.app_hom, Action.comp_hom, cohomology_map_hom,
        restrictionCohomologyFunctorIso_hom_app_hom, Functor.comp_map,
        Action.res_map_hom, restrictGroup_forget]
      change (D.forget.cohomology q).map a ≫ 𝟙 _ = 𝟙 _ ≫ (D.forget.cohomology q).map a
      rw [Category.comp_id, Category.id_comp])

/-- The cohomology restriction comparison is natural in coefficient diagrams. -/
def restrictGroupCohomologyFunctorIso (q : ℕ) :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ cohomologyFunctor q ≅
      cohomologyFunctor q ⋙
        (Functor.whiskeringRight J (Action (ModuleCat.{u} R) G)
          (Action (ModuleCat.{u} R) H)).obj (Action.res (ModuleCat.{u} R) φ) :=
  NatIso.ofComponents (fun D => restrictGroupCohomologyIso φ D q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (restrictionCohomologyFunctorIso R (ρ i) φ q).hom.naturality (α.app i))

/-- The section action diagram of restricted coefficients is the restricted diagram. -/
def restrictGroupSectionsIso (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (restrictGroup φ D).sections ≅ D.sections ⋙ Action.res (ModuleCat.{u} R) φ :=
  NatIso.ofComponents
    (fun i => (restrictionSectionsFunctorIso R (ρ i) φ).app (D.obj i))
    (fun {i j} a => by
      apply Action.Hom.ext
      simp only [Iso.app_hom, Action.comp_hom, sections_map_hom,
        restrictionSectionsFunctorIso_hom_app_hom, Functor.comp_map,
        Action.res_map_hom, restrictGroup_forget]
      change D.forget.sections.map a ≫ 𝟙 _ = 𝟙 _ ≫ D.forget.sections.map a
      rw [Category.comp_id, Category.id_comp])

/-- The section restriction comparison is natural in coefficient diagrams. -/
def restrictGroupSectionsFunctorIso :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ sectionsFunctor ≅
      sectionsFunctor ⋙
        (Functor.whiskeringRight J (Action (ModuleCat.{u} R) G)
          (Action (ModuleCat.{u} R) H)).obj (Action.res (ModuleCat.{u} R) φ) :=
  NatIso.ofComponents (fun D => restrictGroupSectionsIso φ D)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (restrictionSectionsFunctorIso R (ρ i) φ).hom.naturality (α.app i))

/-- Restriction commutes with the canonical degree-zero comparison as a diagram map. -/
theorem restrictGroup_cohomologyZero (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (restrictGroupCohomologyIso φ D 0).hom ≫
        Functor.whiskerRight (cohomologyZeroIso D).hom (Action.res (ModuleCat.{u} R) φ) =
      (cohomologyZeroIso (restrictGroup φ D)).hom ≫
        (restrictGroupSectionsIso φ D).hom := by
  apply NatTrans.ext
  funext i
  exact restriction_cohomologyZero R (ρ i) φ (D.obj i)

/-- Restricting by the identity homomorphism gives the original coefficients. -/
def restrictGroupIdIso :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) (MonoidHom.id G) ≅
      𝟭 (EquivariantCoefficientDiagram R S ρ hρ) :=
  Iso.refl _

variable {K : Type t''} [Group K] (ψ : K →* H)

/-- Successive group restrictions agree with restriction along the composite. -/
def restrictGroupCompIso :
    restrictGroupFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) φ ⋙
        restrictGroupFunctor ψ ≅
      restrictGroupFunctor (φ.comp ψ) :=
  Iso.refl _

variable {I : Type v'} [Category.{w'} I] (F : I ⥤ J)

/-- Change of index and restriction of the acting group commute naturally. -/
def reindexRestrictGroupIso :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙ restrictGroupFunctor φ ≅
      restrictGroupFunctor φ ⋙ reindexFunctor F :=
  Iso.refl _

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
