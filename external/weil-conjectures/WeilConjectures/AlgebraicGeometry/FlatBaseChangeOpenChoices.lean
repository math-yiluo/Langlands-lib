/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.Topology.OpenModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Restricted resolution choices for the section formula

Source: Stacks Project, Cohomology, Tags 01FB and 01E4
(blueprint: def-weil-pbc-flat-base-change-open-choices).
-/

@[expose] public section

universe uOpen
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Cohomology of the presheaf of section complexes: V ↦ H^p(K(V)).
Source: Stacks, Tag 01E4 (blueprint: def-weil-pbc-flat-base-change-open-choices). -/
def sectionCohomologyPresheaf {Y : Scheme.{uOpen}} (K : CochainComplex Y.Modules ℕ) (p : ℕ) :
    _root_.PresheafOfModules.{uOpen} Y.ringCatSheaf.obj :=
  ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K |>.homology p

/-- The canonical sheafification comparison: commute exact sheafification with homology,
then apply the counit on the section complex.
Source: Stacks, Tag 01E4 (blueprint: def-weil-pbc-flat-base-change-open-choices). -/
def sectionCohomologyComparison {Y : Scheme.{uOpen}} (K : CochainComplex Y.Modules ℕ)
    (p : ℕ) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
      (sectionCohomologyPresheaf K p) ⟶ K.homology p :=
  (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj))).inv ≫
    (HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℕ) p).map
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y.ringCatSheaf.obj)).counit.mapHomologicalComplex (ComplexShape.up ℕ)).app K)

/-- The canonical cocycle-to-cohomology-sheaf map theta of Stacks 01E4, adjoint to the
preceding comparison: a class of a cocycle s ∈ K^p(V) goes to the section of H^p(K)
over V defined by s.
Source: Stacks, Tag 01E4 (blueprint: def-weil-pbc-flat-base-change-open-choices). -/
def sectionCohomologyTheta {Y : Scheme.{uOpen}} (K : CochainComplex Y.Modules ℕ) (p : ℕ) :
    sectionCohomologyPresheaf K p ⟶
      (SheafOfModules.forget Y.ringCatSheaf).obj (K.homology p) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _
    (sectionCohomologyComparison K p)

/-- A resolution of the restriction, identified with the restricted original resolution
by an augmentation-preserving isomorphism. Sections are identified by restrictAppIso.
Source: Stacks, Tags 01E1 and 01E4
(blueprint: def-weil-pbc-flat-base-change-open-choices). -/
structure RestrictedResolutionSections {X : Scheme.{uOpen}} {F : X.Modules}
    (I : InjectiveResolution F) (U : X.Opens) where
  resolution : InjectiveResolution ((restrictFunctor U.ι).obj F)
  comparison : resolution.cocomplex ≅
    ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  augmentation : resolution.ι.f 0 ≫ comparison.hom.f 0 =
    (restrictFunctor U.ι).map (I.ι.f 0)
  sections : ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{uOpen}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      resolution.cocomplex ≅
    ((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex
  components : ∀ n : ℕ, sections.hom.f n =
    Hom.app (comparison.hom.f n) ⊤ ≫
      (restrictAppIso U.ι (I.cocomplex.X n) ⊤).hom ≫
        (I.cocomplex.X n).presheaf.map (eqToHom U.ι_image_top.symm).op

/-- Choices identifying the recorded cohomology h-map on an inverse-image open with
section complexes of the original resolutions. The restricted h-map is pinned by the
restriction-unit square, and both resolution identifications preserve augmentations.
The section identifications are pinned degreewise to restriction of sections.
Source: Stacks, Tags 01FB, 01E4
(blueprint: def-weil-pbc-flat-base-change-open-choices). -/
structure FlatBaseChangeOpenChoices {X S S' : Scheme.{uOpen}}
    (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens) where
  psi : (restrictFunctor (f ⁻¹ᵁ V).ι).obj F ⟶
    (pushforward ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)).obj
      ((restrictFunctor ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
        ((tensorPullback (pullback.snd g f)).obj F))
  unit_square :
    (restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app F ≫
      (pushforward (f ⁻¹ᵁ V).ι).map psi ≫
      (pushforwardComp ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
        ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) (f ⁻¹ᵁ V).ι).hom.app
          ((restrictFunctor ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((tensorPullback (pullback.snd g f)).obj F)) ≫
      (pushforwardCongr ((pullback.snd g f).resLE_comp_ι
        (U := f ⁻¹ᵁ V) (V := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)).hom.app
          ((restrictFunctor ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((tensorPullback (pullback.snd g f)).obj F)) =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map
          ((restrictAdjunction ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
            ((tensorPullback (pullback.snd g f)).obj F)) ≫
        (pushforwardComp ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          (pullback.snd g f)).hom.app
            ((restrictFunctor ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
              ((tensorPullback (pullback.snd g f)).obj F))
  source : RestrictedResolutionSections I (f ⁻¹ᵁ V)
  target : RestrictedResolutionSections J ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))

/-- The equality of the two inverse-image opens, induced by the fibre-product square.
Source: Stacks, Tag 01E4 (blueprint: def-weil-pbc-flat-base-change-open-choices).
Proof: apply inverse image of V to the fibre-product projection identity, and use
Scheme.Hom.comp_preimage to identify both composite inverse images. -/
theorem flatBaseChangeOpenEquality {X S S' : Scheme.{uOpen}}
    (f : X ⟶ S) (g : S' ⟶ S) (V : S.Opens) :
    (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V) = (pullback.fst g f) ⁻¹ᵁ (g ⁻¹ᵁ V) :=
  by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

/-- Transport a cohomology class of a restricted resolution to a section of its
cohomology sheaf. Every arrow is a specified resolution/evaluation comparison or theta.
Source: Stacks, Tag 01E4 (blueprint: def-weil-pbc-flat-base-change-open-choices). -/
def resolutionSectionClass {Z Y : Scheme.{uOpen}} {G : Z.Modules}
    (R : InjectiveResolution G) (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (a : ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uOpen}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.cocomplex ≅
      ((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{uOpen}).obj
      ((RingedSpace.moduleCohomology Z.toRingedSpace p).obj G) ⟶
        (K.homology p).presheaf.obj (op V) :=
  letI := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  (forget₂ _ AddCommGrpCat.{uOpen}).map
    (R.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p).hom ≫
    (((RingedSpace.globalSectionsComplex R).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uOpen})).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{uOpen} (ComplexShape.up ℕ) p).map
      a.hom ≫
    (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
          (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{uOpen}).obj (op V))).hom ≫
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      (sectionCohomologyTheta K p)).app (op V)

end AlgebraicGeometry.Scheme.Modules
