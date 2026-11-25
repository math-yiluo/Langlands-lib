/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictedLiftSectionsCore
import WeilConjectures.AlgebraicGeometry.RestrictionResolutionLiftSections

/-! # The section formula for the restricted lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-pbc-restricted-lift-section-formula).
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

private theorem openSections_map {Y : Scheme.{uBC}} {M N : Y.Modules}
    (φ : M ⟶ N) (U : Y.Opens) :
    (RingedSpace.openModuleSections Y.toRingedSpace U).map φ = Hom.app φ U := rfl

/-- The section identity for the explicit restriction-adjunction lift.
Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-pbc-restricted-lift-section-formula).
Proof: Check the equality in every degree. Expand the restriction-adjunction lift
using its counit formula. Evaluate that counit and both pushforward composition
comparisons on the top open. These maps are restrictions along equal inverse-image
opens. Use D.source.components and D.target.components to identify the section
comparisons with the same restriction maps; use ha for the pushforward/global
sections comparison. Naturality moves the resolution comparison maps across these
restrictions, and each comparison cancels its inverse. Functoriality of presheaf
restriction combines the remaining maps. The pullback projection identity gives
flatBaseChangeOpenEquality, so the residual map is precisely evaluation of the
pushforward square in flatBaseChangeResolutionQ. No augmentation equation is used.
The proof works for any t and does not pass to homology. -/
theorem flatBaseChangeRestrictedLift_section_formula {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) :
    let h := (pullback.snd g f).resLE (f ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl
    let ΓS := (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
    let ΓT := (RingedSpace.globalSectionsFunctor
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
    ∀ (a : ΓT.obj D.target.resolution.cocomplex ≅
        ΓS.obj (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.resolution.cocomplex)),
      (∀ n : ℕ, a.inv.f n =
        (Scheme.Modules.presheaf (D.target.resolution.cocomplex.X n)).map
          (eqToHom (by simp) :
            (⊤ : ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.Opens) ⟶
              h ⁻¹ᵁ (⊤ : (f ⁻¹ᵁ V).toScheme.Opens)).op) →
      ((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t) =
      D.source.sections.inv ≫ ΓS.map (flatBaseChangeRestrictedLift f g I J t V D) ≫ a.inv ≫
        (D.target.sections ≪≫ eqToIso (congrArg (fun U ↦
          ((RingedSpace.openModuleSections
            (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj J.cocomplex)
              (flatBaseChangeOpenEquality f g V))).hom := by
  intro h ΓS ΓT a ha
  let E := (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let e := eqToIso (congrArg (fun U ↦
    ((RingedSpace.openModuleSections
      (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
      (flatBaseChangeOpenEquality f g V))
  have liftSections : ΓS.map (flatBaseChangeRestrictedLift f g I J t V D) ≫
      a.inv ≫ D.target.sections.hom = D.source.sections.hom ≫ E.map t := by
    exact restrictionResolutionLift_sections (pullback.snd g f) I J t
      (f ⁻¹ᵁ V) D.source D.target a ha
  have squareSections :
      ((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t) =
      E.map t ≫ e.hom := by
    ext n : 1
    dsimp only [E, e, flatBaseChangeResolutionQ, flatBaseChangePushforwardSquare,
      Functor.mapHomologicalComplex, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex]
    simp only [Functor.map_comp, HomologicalComplex.comp_f, Iso.trans_hom, Iso.symm_hom]
    simp only [openSections_map]
    simp only [Hom.comp_app, pushforward_map_app, NatTrans.comp_app,
      pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app, Category.comp_id,
      eqToHom_op, eqToHom_map]
    simp only [eqToIso.hom, HomologicalComplex.eqToHom_f]
    rfl
  have hl := congrArg (fun z ↦ D.source.sections.inv ≫ z ≫ e.hom) liftSections
  exact squareSections.trans (by
    simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc] using hl.symm)


end AlgebraicGeometry.Scheme.Modules
