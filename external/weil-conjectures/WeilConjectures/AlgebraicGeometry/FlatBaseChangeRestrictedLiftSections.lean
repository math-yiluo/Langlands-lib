/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictedLiftAugmentation
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictedLiftSectionsFormula

/-! # The restriction square on section complexes

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
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

/-- Restriction along inverse-image top identifies global sections of pushforward. -/
private def restrictedLiftSectionsIso {Y Z : Scheme.{uBC}} (h : Y ⟶ Z)
    (A : CochainComplex Y.Modules ℕ) :
    ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ≅
    ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A) := by
  refine (HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (presheaf (A.X n)).mapIso
      (eqToIso (by simp) : op (h ⁻¹ᵁ (⊤ : Z.Opens)) ≅ op (⊤ : Y.Opens))) ?_).symm
  intro n m _
  change (presheaf (A.X n)).map _ ≫
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (A.d n m)).app _ =
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (A.d n m)).app _ ≫
      (presheaf (A.X m)).map _
  exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (A.d n m)).naturality _

/-- Restriction of an augmented lift, together with its canonical section square.
Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-pbc-flat-base-change-restricted-lift-sections).

Proof: Put U = f inverse-image V and W = g' inverse-image U. Restrict t to U,
then conjugate its source and target by the augmentation-preserving comparisons
in D. Use the restriction/direct-image comparison for g' to obtain k. The
augmentation equation for t and D.unit_square give the augmentation equation
for k, by the restriction adjunction. Construct a degreewise by restriction of
sections along h inverse-image top = top; naturality makes it a complex iso.
Expand the pushforward square defining q. Its components are restriction of
sections along the pullback projection identity. The component equations in
D identify the source and target section comparisons with the same restriction
maps. Thus q is the conjugate of the section map of k by these comparisons.
This is an equality of complex maps, checked in each degree; it uses no homology. -/
theorem flatBaseChangeRestrictedLift_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) :
    let h := (pullback.snd g f).resLE (f ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl
    let ΓS := (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
    let ΓT := (RingedSpace.globalSectionsFunctor
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
    ∃ (k : D.source.resolution.cocomplex ⟶
        ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.resolution.cocomplex)
      (a : ΓT.obj D.target.resolution.cocomplex ≅
        ΓS.obj (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.resolution.cocomplex)),
      D.source.resolution.ι.f 0 ≫ k.f 0 =
        D.psi ≫ (pushforward h).map (D.target.resolution.ι.f 0) ∧
      (∀ n : ℕ, a.inv.f n =
        (Scheme.Modules.presheaf (D.target.resolution.cocomplex.X n)).map
          (eqToHom (by simp) :
            (⊤ : ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.Opens) ⟶
              h ⁻¹ᵁ (⊤ : (f ⁻¹ᵁ V).toScheme.Opens)).op) ∧
      ((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t) =
      D.source.sections.inv ≫ ΓS.map k ≫ a.inv ≫
        (D.target.sections ≪≫ eqToIso (congrArg (fun U ↦
          ((RingedSpace.openModuleSections
            (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj J.cocomplex)
              (flatBaseChangeOpenEquality f g V))).hom := by
  let h := (pullback.snd g f).resLE (f ⁻¹ᵁ V)
    ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl
  let a := restrictedLiftSectionsIso h D.target.resolution.cocomplex
  have ha : ∀ n : ℕ, a.inv.f n =
      (Scheme.Modules.presheaf (D.target.resolution.cocomplex.X n)).map
        (eqToHom (by simp) :
          (⊤ : ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.Opens) ⟶
            h ⁻¹ᵁ (⊤ : (f ⁻¹ᵁ V).toScheme.Opens)).op := by
    intro n
    rfl
  refine ⟨flatBaseChangeRestrictedLift f g I J t V D, a,
    flatBaseChangeRestrictedLift_augmentation f g I J t ht V D, ha, ?_⟩
  exact flatBaseChangeRestrictedLift_section_formula f g I J t V D a ha

end AlgebraicGeometry.Scheme.Modules
