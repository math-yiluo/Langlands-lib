/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionOpenMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictedLiftSections
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyAugmentedLift

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

-- Elaborating restriction and section transports uses several nested complex functors.
/-- Before sheafification, the section map of the augmented lift computes the h-map.
Source: Stacks Project, Cohomology, Tags 01FB, 01EZ and 02N7.
(blueprint: lem-weil-pbc-flat-base-change-restricted-lift-homology).

Proof: Restrict t to U = f⁻¹V. Conjugate by D.source.comparison and
D.target.comparison and by the restriction/direct-image comparison to obtain a map
from D.source.resolution to h_*D.target.resolution, where h is the restricted g'.
The augmentation equations of both comparisons and D.unit_square identify its
augmentation with D.psi. Resolve h_*D.target.resolution by a quasi-isomorphism
lambda into a complex of injectives. Compose the restricted lift with lambda for
the horizontal map in ModuleCohomologyFMapData. The canonical comparison of sections
is pinned degreewise by the fields D.source.components and D.target.components;
the pushforward square and equality of inverse-image opens identify this horizontal
section map with the section map of flatBaseChangeResolutionQ. Tag 01EZ makes the
homology of sections of lambda invertible. In the definition of the cohomology map,
cancel that homology map with its inverse. Independence of ModuleCohomologyFMapData
identifies the resulting map with moduleCohomologyFMap. The remaining comparisons
are exactly the two resolution and forgetful homology comparisons in the open map.
The inverse target comparison cancels, proving equality with the cohomology h-map. -/
theorem flatBaseChangeRestrictedLift_homology {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (p : ℕ) (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) :
    flatBaseChangeResolutionOpenMap f g I J t p V D =
      moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
        ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p := by
  let := RingedSpace.globalSectionsFunctor_additive (f ⁻¹ᵁ V).toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive
    ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace
  obtain ⟨k, a, hk, ha, hs⟩ := flatBaseChangeRestrictedLift_sections f g I J t ht V D
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p
  let rG := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
    (D.source.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex D.source.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uBC})).symm
  let rF := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
    (D.target.resolution.isoRightDerivedObj (RingedSpace.globalSectionsFunctor
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex D.target.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uBC})).symm
  let aT := D.target.sections ≪≫
    eqToIso (congrArg (fun U ↦ ((RingedSpace.openModuleSections
      (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (flatBaseChangeOpenEquality f g V))
  let ΓS := (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
  let q := ((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t)
  have hq : q = D.source.sections.inv ≫ ΓS.map k ≫ a.inv ≫ aT.hom := hs
  have hc := moduleCohomologyFMap_of_augmentedLift _ D.psi
    D.target.resolution D.source.resolution k hk a ha p
  change rG.hom ≫ H.map (ΓS.map k) ≫ (H.mapIso a).inv ≫ rF.inv = _ at hc
  change (rG ≪≫ H.mapIso D.source.sections).hom ≫ H.map q ≫
    (rF ≪≫ H.mapIso aT).inv = _
  calc
    _ = (rG ≪≫ H.mapIso D.source.sections).hom ≫
        H.map (D.source.sections.inv ≫ ΓS.map k ≫ a.inv ≫ aT.hom) ≫
          (rF ≪≫ H.mapIso aT).inv :=
      congrArg (fun z ↦ (rG ≪≫ H.mapIso D.source.sections).hom ≫ H.map z ≫
        (rF ≪≫ H.mapIso aT).inv) hq
    _ = rG.hom ≫ H.map (ΓS.map k) ≫ (H.mapIso a).inv ≫ rF.inv := by
      simp only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
        Functor.mapIso_inv, Category.assoc]
      simp only [Functor.map_hom_inv'_assoc]
    _ = _ := hc

end AlgebraicGeometry.Scheme.Modules
