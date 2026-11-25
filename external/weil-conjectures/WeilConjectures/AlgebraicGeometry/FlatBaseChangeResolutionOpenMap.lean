/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # The open cohomology map of a fixed resolution lift

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

/-- The map of open cohomology computed directly from t on section complexes.
Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: def-weil-pbc-flat-base-change-resolution-open-map).
The source and target homology isomorphisms are the canonical resolution comparisons,
forgetful homology comparisons, and the section isomorphisms pinned by D. No replacement
complex, arbitrary witness, or unproved choice is used in this construction. -/
def flatBaseChangeResolutionOpenMap {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (p : ℕ) (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) :
    (forget₂ _ AddCommGrpCat.{uBC}).obj
      ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ⟶
    (forget₂ _ AddCommGrpCat.{uBC}).obj
      ((RingedSpace.moduleCohomology
        ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
          ((restrictFunctor ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((tensorPullback (pullback.snd g f)).obj F))) :=
  letI := RingedSpace.globalSectionsFunctor_additive (f ⁻¹ᵁ V).toScheme.toRingedSpace
  letI := RingedSpace.globalSectionsFunctor_additive
    ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p
  let rS := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
    (D.source.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex D.source.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uBC})).symm ≪≫ H.mapIso D.source.sections
  let aT := D.target.sections ≪≫
    eqToIso (congrArg (fun U ↦ ((RingedSpace.openModuleSections
      (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (flatBaseChangeOpenEquality f g V))
  let rT := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
    (D.target.resolution.isoRightDerivedObj (RingedSpace.globalSectionsFunctor
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex D.target.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uBC})).symm ≪≫ H.mapIso aT
  let qV := ((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t)
  rS.hom ≫ H.map qV ≫ rT.inv

end AlgebraicGeometry.Scheme.Modules
