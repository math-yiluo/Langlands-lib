/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Evaluation comparison from raw derived Hom to restricted cohomology

Source: Stacks Project, Tags 03Q8, 072W and 0BKV.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

namespace RawRestrictedComparison

/-- The existing stability instance, named to avoid unfolding etaleness during synthesis.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
abbrev etaleComposition : MorphismProperty.IsStableUnderComposition @Etale := inferInstance

/-- The existing identity instance, named to avoid unfolding etaleness during synthesis.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
abbrev etaleIdentities : MorphismProperty.ContainsIdentities @Etale := inferInstance

/-- Etaleness is stable under the pullbacks used here.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
theorem etalePullbacks {X Y : Scheme.{v}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong (@Etale) f := inferInstance

/-- The existing base-change stability instance in an explicit form.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
theorem etaleBaseChange {X Y : Scheme.{v}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Etale) f := inferInstance

attribute [local instance] etaleComposition etaleIdentities etalePullbacks
  etaleBaseChange

set_option backward.isDefEq.respectTransparency true in
/-- Cache the existing sheafification instance during elaboration of the formulas.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
theorem sheafifyInstance (X : Scheme.{v}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{v + 1} := inferInstance

set_option backward.isDefEq.respectTransparency true in
/-- Cache the weak instance underlying the same sheafification.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
theorem weakSheafifyInstance (X : Scheme.{v}) :
    HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{v + 1} := inferInstance

attribute [local instance] sheafifyInstance weakSheafifyInstance

set_option backward.isDefEq.respectTransparency true in
/-- The free abelian represented sheaf whose inverse image is the raw Hom source.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable abbrev freeSheaf (S : Scheme.{v}) (U : S.Etale) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} :=
  (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
    (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free)

set_option backward.isDefEq.respectTransparency false in
/-- Sections of an etale restriction are sections over the etale object.
The terminal object of the localized site maps to that object.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def sectionsIso {Y : Scheme.{v}} (W : Y.Etale)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      ((upperStar AddCommGrpCat.{v + 1} W.hom).obj G) ≅ G.obj.obj (op W) := by
  let i : (MorphismProperty.Over.map ⊤ W.prop).obj
      (Scheme.Etale.mk (𝟙 W.left)) ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by rfl)
  exact (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).mapIso
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{v + 1} W.hom W.prop).app G) ≪≫
    (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale W.left)).app _ ≪≫ G.obj.mapIso i.op.symm

set_option backward.isDefEq.respectTransparency false in
/-- The represented identity section, pulled back to `U ×_S Y`.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def generator {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale) :
    (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      ((upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj
        ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))) := by
  let A := freeSheaf S U
  let G := (upperStar AddCommGrpCat.{v + 1} h).obj A
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let x : A.obj.obj (op U) :=
    (toSheafify S.smallEtaleTopology
      (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U)
        (FreeAbelianGroup.of (ULift.up (𝟙 U)))
  exact (sectionsIso W G).inv
    (((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).unit.app A).hom.app (op U) x)

namespace Evaluation

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [HasKInjectiveResolutions D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (R : D ⥤ AddCommGrpCat.{v + 1}) [R.Additive] [PreservesFiniteLimits R]

/-- Restriction followed by derived sections, in abstract abelian categories.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable abbrev functor : DerivedCategory.Plus C ⥤ DerivedCategory AddCommGrpCat.{v + 1} :=
  DerivedCategory.Plus.ι ⋙ L.mapDerivedCategory ⋙ R.rightDerivedFunctor

/-- The degree-zero single comparison for evaluation.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def singleIso (F : C) :
    (functor L R).obj ((DerivedCategory.Plus.singleFunctor C 0).obj F) ≅
      R.rightDerivedFunctor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor D 0).obj (L.obj F))) :=
  R.rightDerivedFunctor.mapIso
    (L.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso C 0).app F) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctorIsoCompQ D 0).app (L.obj F))

/-- Zeroth derived evaluation is underived evaluation.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def zeroIso (F : C) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
      ((functor L R).obj ((DerivedCategory.Plus.singleFunctor C 0).obj F)) ≅
        R.obj (L.obj F) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).mapIso
    (R.rightDerivedFunctor.mapIso
      (L.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso C 0).app F) ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    R.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj F) 0 ≪≫
    R.rightDerivedZeroIsoSelf.app (L.obj F)

/-- Undo the shift after taking zeroth homology.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def shiftIso (p : ℕ) (F : C) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
      ((functor L R).obj (((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦(p : ℤ)⟧)) ≅
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).obj
      (R.rightDerivedFunctor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor D 0).obj (L.obj F)))) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).mapIso
      (((functor L R).commShiftIso (p : ℤ)).app _) ≪≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).shiftIso
      (p : ℤ) 0 (p : ℤ) (by simp)).app _ ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).mapIso (singleIso L R F)

/-- Apply an additive functor to a morphism and evaluate at a fixed element.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def evaluate {E : Type*} [Category.{v + 1} E] [Preadditive E]
    (T : E ⥤ AddCommGrpCat.{v + 1}) [T.Additive] {A B : E} (x : T.obj A) :
    AddCommGrpCat.of (A ⟶ B) ⟶ T.obj B :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ T.map f x
      map_zero' := by simp
      map_add' := fun f g ↦ by simp }

end Evaluation

/-- Restrict a bounded-below derived object, then take derived sections.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable abbrev sectionsFunctor {Y : Scheme.{v}} (W : Y.Etale) :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ⥤
      DerivedCategory AddCommGrpCat.{v + 1} :=
  Evaluation.functor (upperStar AddCommGrpCat.{v + 1} W.hom)
    (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1})

/-- Zeroth derived sections of a single sheaf are its sections.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def zeroIso {Y : Scheme.{v}} (W : Y.Etale)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
      ((sectionsFunctor W).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
    (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      ((upperStar AddCommGrpCat.{v + 1} W.hom).obj F) :=
  Evaluation.zeroIso (upperStar AddCommGrpCat.{v + 1} W.hom)
    (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}) F

/-- Shifted zeroth derived sections compute degree p restricted cohomology.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def shiftIso {S Y : Scheme.{v}} (h : Y ⟶ S) (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
      ((sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)) ≅
      rawAffineRestrictedCohomology h p F U :=
  Evaluation.shiftIso (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
    (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) p F

end RawRestrictedComparison

set_option backward.isDefEq.respectTransparency false in
/-- Apply restricted derived sections and zeroth homology to a raw class, evaluate
at the pulled-back represented identity section, and undo the shift comparison.
All data are explicit functorial constructions.
Source: Stacks Project, Tag 03Q8; Tags 072W and 0BKV.
(blueprint: def-sbc-raw-restricted-cohomology-comparison-map). -/
noncomputable def rawRestrictedCohomologyComparison {S Y : Scheme.{v}} (h : Y ⟶ S)
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale) :
    (abelianHigherDirectImageRawPresheaf h p F).obj (op U) ⟶
      rawAffineRestrictedCohomology h p F U := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj (RawRestrictedComparison.freeSheaf S U)
  let x := (RawRestrictedComparison.zeroIso W A).inv (RawRestrictedComparison.generator h U)
  have : (rightDerivedGlobalSections AddCommGrpCat.{v + 1} W.left).Additive :=
    inferInstanceAs (Functor.rightDerivedFunctor
      (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1})).Additive
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  exact RawRestrictedComparison.Evaluation.evaluate T x ≫
    (RawRestrictedComparison.shiftIso h p F U).hom

end AlgebraicGeometry.Etale
