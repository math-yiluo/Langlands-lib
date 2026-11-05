import Langlands.Geometry.EtaleEquivariantPullbackCoherence
import Langlands.Geometry.EtaleSchemeDeckAction
import Langlands.Geometry.EtaleDeckAction
import Langlands.Geometry.EtaleInverseImageRestrictionCoherence

/-! # Agreement of canonical scheme deck actions with etale restriction -/

noncomputable section

universe u t wY wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleSchemeDeckAction

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections EtaleCohomologyAction
open EtalePullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} {G : Type t} [Group G]
variable (τ : G →* (Aut Y)ᵐᵒᵖ) (p : Y ⟶ X) [Etale p]
variable (hp : ∀ g, (aut τ g).hom ≫ p = p)
variable (R : Type u) [CommRing R]

/-- The earlier deck coefficient structure is the original restriction
composition comparison followed by the actual deck triangle. -/
theorem restrictionCoefficient_act (M : ModuleSheaf X R) (g : G) :
    ((deckEquivariantFunctor R τ p hp).obj M).act g =
      (restrictionComp p (ModuleCat.{u} R) (aut τ g).hom).hom.app M ≫
        (restrictionCongr R (hp g)).hom.app M := by
  rw [deckEquivariantFunctor_obj_act]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [equivariantRestrictionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  simp only [restrictionCongr_inv_component,
    EtaleCohomologyAction.restrictionCongr_hom_component]
  dsimp [restrictionComp, restrictionId, restriction, translateBy,
    EtaleAutomorphism.translate, EtaleAutomorphism.sheafEquivalence]
  simp only [Category.comp_id, ← M.obj.map_comp]
  congr 1

/-- The actual inverse-image coefficient comparison of an etale triangle
agrees with restriction composition and equality transport. -/
theorem projectionInverseImageIso_restriction {Z : Scheme.{u}}
    (q : Z ⟶ X) [Etale q] (f : Z ⟶ Y) [Etale f] (hf : f ≫ p = q)
    (M : ModuleSheaf X R) :
    (projectionInverseImageIso R p q f hf).hom.app M ≫
        (inverseImageIsoRestriction q R).hom.app M =
      (inverseImage f R).map ((inverseImageIsoRestriction p R).hom.app M) ≫
        (inverseImageIsoRestriction f R).hom.app
          ((restriction p (ModuleCat.{u} R)).obj M) ≫
        (restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
        (restrictionCongr R hf).hom.app M := by
  have hc := congrArg (fun a => a.app M) (inverseImageIsoRestriction_comp R p f)
  have he := congrArg (fun a => a.app M) (inverseImageIsoRestriction_congr R hf)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hc he
  dsimp only [projectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, he, ← Category.assoc, hc]
  simp only [Category.assoc]

/-- The constructed inverse-image deck coefficients identify with the earlier
restriction deck coefficients under the specified canonical isomorphisms. -/
theorem coefficientIso_restriction (M : ModuleSheaf X R) (g : G) :
    (coefficientIso τ p hp R g).hom.app M ≫
        (inverseImageIsoRestriction p R).hom.app M =
      (inverseImage (aut τ g).hom R).map
          ((inverseImageIsoRestriction p R).hom.app M) ≫
        (inverseImageIsoRestriction (aut τ g).hom R).hom.app
          ((restriction p (ModuleCat.{u} R)).obj M) ≫
        ((deckEquivariantFunctor R τ p hp).obj M).act g := by
  simpa only [coefficientIso, restrictionCoefficient_act, Category.assoc] using
    projectionInverseImageIso_restriction p R p (aut τ g).hom (hp g) M

section Consumers

variable [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- The canonical coefficient isomorphism identifies the actual derived deck
functor with the earlier restriction functor, including the original action. -/
def derivedRestrictionIso :
    derivedFunctor τ p hp R ≅ deckDerivedSectionsFunctor R τ p hp :=
  NatIso.ofComponents (fun M => Action.mkIso
    ((EtaleDerivedSectionsPlus.derivedSections Y R).mapIso
      ((inverseImageIsoRestriction p R).app M))
    (fun g => by
      rw [derivedFunctor_obj_ρ]
      change EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients
          (aut τ g).hom R ((coefficientIso τ p hp R g).hom.app M) ≫
            (EtaleDerivedSectionsPlus.derivedSections Y R).map
              ((inverseImageIsoRestriction p R).hom.app M) =
        (EtaleDerivedSectionsPlus.derivedSections Y R).map
          ((inverseImageIsoRestriction p R).hom.app M) ≫
            derivedSectionsMapWithCoefficients (aut τ g).hom R
              (((deckEquivariantFunctor R τ p hp).obj M).act g)
      rw [← EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_postcomp,
        coefficientIso_restriction,
        EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_precomp,
        EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_restriction]))
    (fun {M N} α => by
      apply Action.Hom.ext
      exact (Functor.whiskerRight (inverseImageIsoRestriction p R).hom
        (EtaleDerivedSectionsPlus.derivedSections Y R)).naturality α)

/-- The comparison is exactly derived sections of the canonical coefficient
comparison, rather than an unspecified isomorphism. -/
@[simp] theorem derivedRestrictionIso_hom_app_hom (M : ModuleSheaf X R) :
    ((derivedRestrictionIso τ p hp R).hom.app M).hom =
      (EtaleDerivedSectionsPlus.derivedSections Y R).map
        ((inverseImageIsoRestriction p R).hom.app M) := rfl

/-- Ordinary cohomology comparisons induced by the derived comparison and
the specified recovery isomorphisms on both sides. -/
def cohomologyRestrictionIso (n : ℕ) :
    cohomologyFunctor τ p hp R n ≅ deckCohomologyFunctor R τ p hp n :=
  (homologyFunctorIso τ p hp R n).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictionIso τ p hp R)
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≪≫
    deckDerivedHomologyIso R τ p hp n

/-- The induced ordinary comparison is precisely cohomology of the canonical
coefficient comparison. -/
@[simp] theorem cohomologyRestrictionIso_hom_app_hom (n : ℕ)
    (M : ModuleSheaf X R) :
    ((cohomologyRestrictionIso τ p hp R n).hom.app M).hom =
      (EtaleDerivedSections.cohomology Y R n).map
        ((inverseImageIsoRestriction p R).hom.app M) := by
  have hn := (EtaleDerivedSectionsPlus.homologyNatIso Y R n).hom.naturality
    ((inverseImageIsoRestriction p R).hom.app M)
  dsimp only [Functor.comp_map] at hn
  change (EtaleDerivedSectionsPlus.homologyNatIso Y R n).inv.app
        ((inverseImage p R).obj M) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((EtaleDerivedSectionsPlus.derivedSections Y R).map
          ((inverseImageIsoRestriction p R).hom.app M)) ≫
      (𝟙 _ ≫ (EtaleDerivedSectionsPlus.homologyNatIso Y R n).hom.app
        ((restriction p (ModuleCat.{u} R)).obj M)) = _
  rw [Category.id_comp, hn]
  simp only [Iso.inv_hom_id_app_assoc]

/-- Ordinary sections agree by the derived degree-zero comparison and the
specified recovery isomorphisms on both sides. -/
def sectionsRestrictionIso :
    sectionsFunctor τ p hp R ≅ deckSectionsFunctor R τ p hp :=
  (derivedZeroFunctorIso τ p hp R).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictionIso τ p hp R)
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≪≫
    deckDerivedZeroIso R τ p hp

/-- The induced section comparison is precisely sections of the canonical
coefficient comparison. -/
@[simp] theorem sectionsRestrictionIso_hom_app_hom (M : ModuleSheaf X R) :
    ((sectionsRestrictionIso τ p hp R).hom.app M).hom =
      (EtaleDerivedSections.sections Y R).map
        ((inverseImageIsoRestriction p R).hom.app M) := by
  have hn := (EtaleDerivedSectionsPlus.homologyZeroIso Y R).hom.naturality
    ((inverseImageIsoRestriction p R).hom.app M)
  dsimp only [Functor.comp_map] at hn
  change (EtaleDerivedSectionsPlus.homologyZeroIso Y R).inv.app
        ((inverseImage p R).obj M) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        ((EtaleDerivedSectionsPlus.derivedSections Y R).map
          ((inverseImageIsoRestriction p R).hom.app M)) ≫
      (𝟙 _ ≫ ((pullbackDerivedZeroFunctorIso R τ).hom.app
        ((deckEquivariantFunctor R τ p hp).obj M)).hom) = _
  rw [Category.id_comp, pullbackDerivedZeroFunctorIso_hom_app_hom]
  erw [hn]
  simp only [Iso.inv_hom_id_app_assoc]

/-- Restriction comparison preserves the specified homology recovery as an
equality of full equivariant natural transformations. -/
theorem derivedRestrictionIso_homology (n : ℕ) :
    Functor.whiskerRight (derivedRestrictionIso τ p hp R).hom
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≫
      (deckDerivedHomologyIso R τ p hp n).hom =
    (homologyFunctorIso τ p hp R n).hom ≫
      (cohomologyRestrictionIso τ p hp R n).hom := by
  simp only [cohomologyRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Iso.hom_inv_id_assoc]

/-- The same comparison preserves the specified derived degree-zero
recovery of ordinary sections equivariantly and coefficient-naturally. -/
theorem derivedRestrictionIso_zero :
    Functor.whiskerRight (derivedRestrictionIso τ p hp R).hom
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≫
      (deckDerivedZeroIso R τ p hp).hom =
    (derivedZeroFunctorIso τ p hp R).hom ≫
      (sectionsRestrictionIso τ p hp R).hom := by
  simp only [sectionsRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Iso.hom_inv_id_assoc]

/-- The inherited ordinary degree-zero recovery for the earlier restricted
deck functors, using its specified equivariant coefficient comparison. -/
def restrictionCohomologyZeroIso :
    deckCohomologyFunctor R τ p hp 0 ≅ deckSectionsFunctor R τ p hp :=
  Functor.isoWhiskerLeft (deckEquivariantFunctor R τ p hp)
    (pullbackCohomologyZeroFunctorIso R τ)

omit [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)] in
/-- Its component is the original canonical ordinary-cohomology comparison. -/
@[simp] theorem restrictionCohomologyZeroIso_hom_app_hom (M : ModuleSheaf X R) :
    ((restrictionCohomologyZeroIso τ p hp R).hom.app M).hom =
      (EtaleDerivedSections.cohomologyZeroIso Y R).hom.app
        ((restriction p (ModuleCat.{u} R)).obj M) :=
  pullbackCohomologyZeroFunctorIso_hom_app_hom R τ _

/-- Ordinary degree-zero recovery also commutes with restriction comparison,
as a square of full equivariant natural transformations. -/
theorem cohomologyRestrictionIso_zero :
    (cohomologyRestrictionIso τ p hp R 0).hom ≫
      (restrictionCohomologyZeroIso τ p hp R).hom =
    (cohomologyZeroFunctorIso τ p hp R).hom ≫
      (sectionsRestrictionIso τ p hp R).hom := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  simp only [NatTrans.comp_app, Action.comp_hom,
    cohomologyRestrictionIso_hom_app_hom, sectionsRestrictionIso_hom_app_hom,
    restrictionCohomologyZeroIso_hom_app_hom, cohomologyZeroFunctorIso_hom_app_hom]
  simp only [EtaleDerivedSectionsPlus.homologyZeroIso, Iso.trans_hom,
    NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
  exact (EtaleDerivedSections.cohomologyZeroIso Y R).hom.naturality
    ((inverseImageIsoRestriction p R).hom.app M)

end Consumers

end Langlands.Geometry.EtaleSchemeDeckAction
