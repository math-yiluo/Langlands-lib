/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluationData
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarFromPointAdditive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Condensed.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace Profinite.CondensedAction.InternalBar

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The actual free-forgetful adjunction, determining the generator inclusion.
Source: step 1, the universal property of the free internal module
(auxiliary; not a blueprint node). -/
def freeAdjunction : free R ⊣
    Mod.forget R.X ⋙ sheafCompose (coherentTopology Profinite.{u})
      (forget AddCommGrpCat.{u + 1}) :=
  (Sheaf.adjunction (coherentTopology Profinite.{u}) AddCommGrpCat.adj.{u + 1}).comp
    (Mod.freeForgetAdjunction R.X)

end Profinite.CondensedAction.InternalBar

namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice

/-- The representable condensed set of a profinite parameter.
Source: Stacks 08FI, 08J7; HRS Section 3 (auxiliary; not a blueprint node). -/
abbrev parameter (P : Profinite.{u}) :=
  ((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice

namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.upperStarFromPoint_additive
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Mod.monoidalCategory Mod.monoidalCategoryStruct
  Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 20000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

section CachedInstances
variable (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
private theorem pointFour : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (PointModules A)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem pointGood12 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (PointModules A)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem pointGood23 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (PointModules A)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem pointLeft : ∀ (X : PointModules A),
    PreservesColimitsOfShape ℤ ((curriedTensor (PointModules A)).obj X) := inferInstance
private theorem pointRight : ∀ (X : PointModules A),
    PreservesColimitsOfShape ℤ ((curriedTensor (PointModules A)).flip.obj X) := inferInstance
variable (T : Scheme.{u})
private theorem schemeFour : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Modules A T)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem schemeGood12 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem schemeGood23 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem schemeLeft : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).obj X) := inferInstance
private theorem schemeRight : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).flip.obj X) := inferInstance
end CachedInstances
attribute [local instance] pointFour pointGood12 pointGood23 pointLeft pointRight
  schemeFour schemeGood12 schemeGood23 schemeLeft schemeRight

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The recorded free module on h_P.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
abbrev freeParameter (P : Profinite.{u}) :=
  (Profinite.CondensedAction.InternalBar.free (Mon.mk R.X)).obj (ProfiniteFreeSlice.parameter P)

/-- The point inverse image preserves finite colimits. -/
instance upperStarFromPoint_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (upperStarFromPoint X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  unfold upperStarFromPoint
  infer_instance

section Scalars
variable (S : Profinite.CondensedRing.{u}) [IsCommMonObj S.X]
  (φ : R.X ⟶ S.X) [IsMonHom φ]

/-- Exact coefficient restriction at the condensed point.
Source: Stacks 03D2 (auxiliary; not a blueprint node). -/
abbrev restrictPoint : PointModules S ⥤ PointModules R := Mod.comap φ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exact coefficient restriction on the small pro-etale site.
Source: Stacks 03D2 (auxiliary; not a blueprint node). -/
abbrev restrictScheme (X : Scheme.{u}) : Modules S X ⥤ Modules R X :=
  Mod.comap (coefficientMap φ X)

/-- The action identification for point pullback and restriction of scalars.
Source: Stacks 03D2 (auxiliary; not a blueprint node). -/
def restrictPointPullD (X : Scheme.{u}) :
    (restrictPoint R S φ).mapDerivedCategory ⋙ pointPullD R X ≅
      pointPullD S X ⋙ (restrictScheme R S φ X).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso ((upperStarFromPoint X).mapModComapIso φ) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The ordinary free-generator coefficient arrow, literally [t] ↦ [t].
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def freeGeneratorScalar (P : Profinite.{u}) :
    freeParameter R P ⟶ (restrictPoint R S φ).obj (freeParameter S P) :=
  ((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk R.X)).homEquiv _ _).symm
    ((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk S.X)).unit.app
      (ProfiniteFreeSlice.parameter P))

attribute [local irreducible] freeGeneratorScalar

set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  DerivedCategory.singleFunctors Profinite.CondensedAction.InternalBar.free
  Mod.comap Mod.extendScalars Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.upperStar CondensedRing.derivedComapUpperStarIso
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

attribute [local irreducible] restrictPointPullD

/-- Canonical scalar/pullback comparison: transpose pullback of the scalar unit
through the action identification. This definition precedes its isomorphism claim.
Source: Stacks 07A6 and 0D6D (auxiliary; not a blueprint node). -/
def scalarPullComparison {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) :
    (Mod.extendScalars (coefficientMap φ Y)).leftDerivedFunctor.obj
      ((CondensedRing.upperStar R.X f).mapDerivedCategory.obj M) ⟶
    (CondensedRing.upperStar S.X f).mapDerivedCategory.obj
      ((Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor.obj M) :=
  ((mateEquiv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ Y))).symm
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)).app M

attribute [local irreducible] scalarPullComparison

/-- Scalar extension commutes with exact geometric inverse image in this normalized form.
Source: Stacks 07A4 and 0D6D, node proof step 9
(auxiliary; not a blueprint node).
Proof: choose a K-flat resolution of M. Geometric inverse image is exact, strong
monoidal and preserves flat objects, so its termwise image computes the pulled
K-flat tensor. The balanced scalar tensor comparison is an isomorphism on each
term, normalized by x ↦ 1 tensor x. It commutes with differentials and descends to
the derived isomorphism. Scalar transposition identifies it with the displayed
scalar-unit formula, so the specified map itself is invertible without flatness
of the coefficient map. -/
@[instance] theorem scalarPullComparison_isIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) : IsIso (scalarPullComparison R S φ f M) := by
  -- Keep the auxiliary ringed-site localization instance local to this call.
  obtain ⟨b, hb⟩ : ∃ b : QuotientChange.D φ X ⋙ QuotientChange.L S.X f ≅
      QuotientChange.L R.X f ⋙ QuotientChange.D φ Y,
      QuotientChange.PullNormalized φ f b := by
    let (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj A] [IsCommMonObj A] (T : Scheme.{u}) :
        HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules A T) :=
      @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
        (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
          (Scheme.ProEt.topology T) _)
    exact QuotientChange.internal_pull_normalization_exists φ f
  let eR : QuotientChange.L R.X f ≅
      (CondensedRing.upperStar R.X f).mapDerivedCategory := by
    unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    exact CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f
  let eS : (CondensedRing.upperStar S.X f).mapDerivedCategory ≅
      QuotientChange.L S.X f := by
    unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f).symm
  let a := (mateEquiv (QuotientChange.scalarAdj φ X)
    (QuotientChange.scalarAdj φ Y)).symm
      (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)
  -- Transport between exact termwise and left-derived geometric pullback.
  have he : (a.whiskerTop eR.hom).whiskerBottom eS.hom =
      (mateEquiv (QuotientChange.scalarAdj φ X)
        (QuotientChange.scalarAdj φ Y)).symm
        (TwoSquare.mk _ _ _ _ (QuotientChange.normalizationRestrictionPull φ f).inv) := by
    apply (mateEquiv (QuotientChange.scalarAdj φ X)
      (QuotientChange.scalarAdj φ Y)).injective
    simp only [a, mateEquiv_whiskerTop_whiskerBottom, Equiv.apply_symm_apply]
    ext M
    delta QuotientChange.normalizationRestrictionPull
    dsimp only [eR, eS, id, TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
    delta QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    dsimp only [TwoSquare.mk, QuotientChange.V, QuotientChange.V₀]
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
  have hi : IsIso (((a.whiskerTop eR.hom).whiskerBottom eS.hom).app M) := by
    rw [he, ← QuotientChange.normalized_inverse φ f b hb]
    infer_instance
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at hi
  have : IsIso (a.app M) := by
    have := IsIso.of_isIso_comp_left
      ((QuotientChange.D φ Y).map (eR.hom.app M))
      (a.app M ≫
        eS.hom.app ((QuotientChange.D φ X).obj M))
    exact IsIso.of_isIso_comp_right _
      (eS.hom.app ((QuotientChange.D φ X).obj M))
  dsimp only [a] at this
  delta QuotientChange.scalarAdj QuotientChange.D at this
  dsimp only [id] at this
  unfold scalarPullComparison
  exact this

end Scalars

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
