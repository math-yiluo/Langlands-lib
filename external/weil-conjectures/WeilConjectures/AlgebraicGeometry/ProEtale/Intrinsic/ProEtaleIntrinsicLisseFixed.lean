/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
public import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
public import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Precoverage.Generates
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Basic.Finite.Prod
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-! # Finite lisse sheaves in the two constant-coefficient presentations -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

namespace ConstantScalarComparison

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  (A : Type (u + 1)) [CommRing A] (R : Sheaf J RingCat.{u + 1})
  (a : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)

private noncomputable def restriction : SheafOfModules.{u + 1} R ⥤
    Sheaf J (ModuleCat.{u + 1} A) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars a).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} A :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars a).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private noncomputable def restrictionFullyFaithful [Presheaf.IsLocallySurjective J a] :
    (restriction J A R a).FullyFaithful where
  preimage {M N} φ :=
    { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective a N.isSheaf).symm
        { app := φ.hom.app
          naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.hom.naturality f) x } }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

variable [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify J (ModuleCat.{u + 1} A)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} A)]

private noncomputable def constantPresheaf (M : ModuleCat.{u + 1} A) :
    PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj _ := M
  map _ := 𝟙 M

private noncomputable def constantComparisonHom (M : ModuleCat.{u + 1} A) :
    (constantSheaf J (ModuleCat.{u + 1} A)).obj M ⟶
      (restriction J A R a).obj
        ((PresheafOfModules.sheafification.{u + 1} a).obj (constantPresheaf A M)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} a).unit.app (constantPresheaf A M)
  exact ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }

private theorem constantComparisonHom_isIso (M : ModuleCat.{u + 1} A) :
    IsIso (constantComparisonHom J A R a M) := by
  let N := (restriction J A R a).obj
    ((PresheafOfModules.sheafification.{u + 1} a).obj (constantPresheaf A M))
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} a).unit.app
    (constantPresheaf A M)
  let η' : (Functor.const Cᵒᵖ).obj M ⟶ N.obj :=
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }
  have hηi : Presheaf.IsLocallyInjective J η' := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf A M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have hηs : Presheaf.IsLocallySurjective J η' := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf A M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have hf : toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
      (constantComparisonHom J A R a M).hom = η' := by
    exact ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Cᵒᵖ).obj M) N).apply_symm_apply η'
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective J (constantComparisonHom J A R a M).hom
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J η' hf
  · change Presheaf.IsLocallySurjective J (constantComparisonHom J A R a M).hom
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf

end ConstantScalarComparison

private theorem localConstancy_iff (T : Scheme.{u}) (B : Type u) [CommRing B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    IsLocallyConstantProEtaleModuleSheaf T B F ↔
      IsLocallyConstantProEtaleFixedModuleSheaf T (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) := by
  let A := ULift.{u + 1, u} B
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B)
  have h (U : T.ProEt) :
      Presheaf.IsLocallyInjective ((ProEt.topology T).over U)
        (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)) ∧
      Presheaf.IsLocallySurjective ((ProEt.topology T).over U)
        (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)) :=
    proEtaleConstantRingUnit_over_locallyBijective T B U
  constructor
  · rintro ⟨I, U, f, hf, he⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := he i
    let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
    have := (h (U i)).1
    have := (h (U i)).2
    let E := ConstantScalarComparison.restriction ((ProEt.topology T).over (U i))
      A (R.over (U i)) a
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a M
    exact ⟨M, ⟨E.mapIso e ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology T).over (U i)) A (R.over (U i)) a M)).symm⟩⟩
  · rintro ⟨I, U, f, hf, he⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := he i
    let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
    have := (h (U i)).1
    have := (h (U i)).2
    let E := ConstantScalarComparison.restriction ((ProEt.topology T).over (U i))
      A (R.over (U i)) a
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a M
    exact ⟨M, ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a).preimageIso
        (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
          ((ProEt.topology T).over (U i)) A (R.over (U i)) a M))⟩⟩

private theorem finite_stalk_iff (T : Scheme.{u}) (B : Type u) [CommRing B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T B) F) ↔
      Finite (proEtaleGeometricFixedModuleStalk x (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F)) := by
  let D := proEtaleGeometricStalkDiagram x ((proEtaleModuleRestriction T B).obj F)
  let e := CategoryTheory.preservesColimitIso
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) D
  constructor
  · intro h
    have : Finite (↑(Limits.colimit (D ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})) :
          Type (u + 1)) := h
    exact Finite.of_equiv _
      (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom)).symm
  · intro h
    have : Finite ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
        AddCommGrpCat.{u + 1}).obj (Limits.colimit D)) := h
    exact Finite.of_equiv _
      (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom))

private theorem finiteLocal_iff (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) ↔
      IsLocallyConstantProEtaleModuleSheaf T B F ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
          Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T B) F) := by
  constructor
  · rintro ⟨ι, W, g, hg, hM⟩
    have hl := ProEtale.finiteModels_over (ULift.{u + 1, u} B) _ ⟨ι, W, g, hg, fun i ↦
      (hM i).imp fun _ ⟨_, e⟩ ↦ ⟨Module.finite_of_finite (ULift.{u + 1, u} B), e⟩⟩
    refine ⟨(localConstancy_iff T B F).mpr ?_, fun Ω _ _ x ↦ ?_⟩
    · obtain ⟨I, U, f, hf, he⟩ := hl
      exact ⟨I, U, f, hf, fun i ↦ ⟨(he i).choose, (he i).choose_spec.2⟩⟩
    · exact (finite_stalk_iff T B F Ω x).mpr
        (ProEtale.finite_geometricStalk_of_finite_models (ULift.{u + 1, u} B) _
          ⟨ι, W, g, hg, fun i ↦ (hM i).imp fun _ ⟨_, e⟩ ↦
            ⟨Module.finite_of_finite (ULift.{u + 1, u} B), e⟩⟩ Ω x)
  · rintro ⟨hl, hs⟩
    obtain ⟨ι, W, g, hg, hM⟩ := finite_models_of_fixed_lisse T (ULift.{u + 1, u} B) _
      ⟨(localConstancy_iff T B F).mp hl,
        fun Ω _ _ x ↦ (finite_stalk_iff T B F Ω x).mp (hs Ω x)⟩
    exact ⟨ι, W, g, hg, fun i ↦ (hM i).imp fun _ ⟨_, e⟩ ↦ ⟨Module.Finite.of_finite, e⟩⟩

end AlgebraicGeometry.Scheme
