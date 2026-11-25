/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Unbounded evaluation comparison for strict coefficient systems

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09T5 and 0D6E.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option linter.unusedSectionVars false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

attribute [local instance] CoefficientEvaluationExtensionData.extensionAdditive

section Abstract
universe a av b bv
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] (a : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedImage_exists [Abelian.HasKInjectiveResolutions B] :
    Nonempty (CoefficientDerivedImage F G a) := by
  let H := G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let W' := HomologicalComplex.quasiIso B (.up ℤ)
  let Φ := CochainComplex.KInjectives.localizerMorphism B
  have hd : Φ.Derives H := by
    intro K I f hf
    have : K.obj.IsKInjective := K.property
    have : I.obj.IsKInjective := I.property
    have hq : QuasiIso f.hom := hf
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f.hom) := by
      rw [← he]
      exact (G.mapHomotopyEquiv e).quasiIso_hom
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map f.hom)))
  have := hd.hasPointwiseRightDerivedFunctor
  let RF := H.totalRightDerived DerivedCategory.Q W'
  let β := H.totalRightDerivedUnit DerivedCategory.Q W'
  have : RF.IsRightDerivedFunctor β W' := by
    dsimp only [RF, β]
    infer_instance
  let LF := F.mapDerivedCategory
  let α := F.mapDerivedCategoryFactors.hom
  have : LF.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W LF F.mapDerivedCategoryFactors
  have : (LF ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.mapDerivedCategoryFactors RF)
  have : (RF ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight β LF ≫ (Functor.associator _ _ _).hom) W' :=
    Φ.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
      (fun I ↦ hd.isIso_of_isRightDerivedFunctor β I) LF
  let ad := (a.mapHomologicalComplex (.up ℤ)).derived W W' α β
  refine ⟨{
    inverse := LF
    inverseFactors := F.mapDerivedCategoryFactors
    direct := RF
    directUnit := β
    isRightDerived := inferInstance
    computes := fun I hI ↦ hd.isIso_of_isRightDerivedFunctor β (.mk I)
    adjunction := ad
    transpose := ?_ }⟩
  intro P I f
  change ad.homEquiv _ _ (α.app P ≫ DerivedCategory.Q.map f) = _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change (((a.mapHomologicalComplex (.up ℤ)).derivedη W α β).app
    (DerivedCategory.Q.obj P) ≫ RF.map (α.app P)) ≫ RF.map (DerivedCategory.Q.map f) = _
  rw [Adjunction.derivedη_fac_app, Category.assoc]
  have hn := β.naturality f
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ β.app I =
    β.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      RF.map (DerivedCategory.Q.map f) at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_unit]

section Square
universe c cv e ev
variable {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type e} [Category.{ev} D] [Abelian D] [HasDerivedCategory.{d} D]
  (eA : A ⥤ C) (eB : B ⥤ D) (Fl : C ⥤ D)
  [eA.Additive] [eB.Additive] [Fl.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (EA : DerivedCategory A ⥤ DerivedCategory C)
  (EB : DerivedCategory B ⥤ DerivedCategory D)
  (FlD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φl : DerivedCategory.Q ⋙ FlD ≅ Fl.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (α : F ⋙ eB ≅ eA ⋙ Fl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem derivedSquare_exists :
    ∃ δ : FD ⋙ EB ≅ EA ⋙ FlD, ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        FlD.map (φA.hom.app P) ≫
        φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
      EB.map (φF.hom.app P) ≫
        φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) := by
  let ψF : DerivedCategory.Q ⋙ (FD ⋙ EB) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φF EB ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φB
  let ψl : DerivedCategory.Q ⋙ (EA ⋙ FlD) ≅
      eA.mapHomologicalComplex (.up ℤ) ⋙
        Fl.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φA FlD ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φl
  let γ := Functor.mapHomologicalComplexCompIso α (.up ℤ)
  let τ := ψF ≪≫ isoWhiskerRight γ DerivedCategory.Q ≪≫ ψl.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D)
  let δ := ff.preimageIso τ
  refine ⟨δ, ?_⟩
  intro P
  have hd : δ.hom.app (DerivedCategory.Q.obj P) = τ.hom.app P := by
    exact congr_app (ff.map_preimage τ.hom) P
  rw [hd]
  dsimp only [τ, ψF, ψl, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← FlD.map_comp_assoc, Iso.inv_hom_id_app]
  erw [FlD.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem derivedSquare_symm_rep
    (δ : FD ⋙ EB ≅ EA ⋙ FlD)
    (hδ : ∀ P, δ.hom.app (DerivedCategory.Q.obj P) ≫
      FlD.map (φA.hom.app P) ≫
      φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
    EB.map (φF.hom.app P) ≫
      φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P)) (P) :
    δ.inv.app (DerivedCategory.Q.obj P) ≫ EB.map (φF.hom.app P) ≫
        φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      FlD.map (φA.hom.app P) ≫
        φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).inv.app P) := by
  apply (cancel_epi (δ.hom.app (DerivedCategory.Q.obj P))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hh := congrArg (fun f ↦ f ≫
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex α (.up ℤ)).inv.app P)) (hδ P)
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app] at hh
  erw [DerivedCategory.Q.map_id, Category.comp_id] at hh
  simpa only [Category.assoc] using hh.symm

end Square

section Mate
universe c cv e ev
variable {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  {Fs : A ⥤ B} {Gs : B ⥤ A} (asys : Fs ⊣ Gs)
  {Fl : C ⥤ D} {Gl : D ⥤ C} (alevel : Fl ⊣ Gl)
  {EA : A ⥤ C} {EB : B ⥤ D} (α : Fs ⋙ EB ≅ EA ⋙ Fl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] in
private theorem evaluation_counit_of_mate (M : B) :
    α.hom.app (Gs.obj M) ≫ Fl.map
        ((mateEquiv asys alevel (TwoSquare.mk _ _ _ _ α.inv)).app M) ≫
        alevel.counit.app (EB.obj M) = EB.map (asys.counit.app M) := by
  rw [mateEquiv_counit, Iso.hom_inv_id_app_assoc]

end Mate

section MateNaturality
universe c cv e ev
variable {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  {Fs : A ⥤ B} {Gs : B ⥤ A} (asys : Fs ⊣ Gs)
  {Fl : C ⥤ D} {Gl : D ⥤ C} (alevel : Fl ⊣ Gl)
  {EA EA' : A ⥤ C} {EB EB' : B ⥤ D}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] in
private theorem mate_whiskerTop (τ : TwoSquare EA Fs Fl EB) (γ : EA' ⟶ EA) :
    mateEquiv asys alevel (τ.whiskerTop γ) =
      (mateEquiv asys alevel τ).whiskerRight γ := by
  ext M
  simp only [mateEquiv, TwoSquare.whiskerTop, TwoSquare.whiskerRight,
    Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, TwoSquare] at τ ⊢
  erw [Category.comp_id]
  have hu := alevel.unit_naturality (γ.app (Gs.obj M))
  simpa only [Category.assoc, Category.comp_id, Category.id_comp,
    Functor.comp_obj, Functor.id_obj] using congrArg (fun f ↦ f ≫
    Gl.map (τ.app (Gs.obj M)) ≫ Gl.map (EB.map (asys.counit.app M))) hu

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] in
private theorem mate_whiskerBottom (τ : TwoSquare EA Fs Fl EB) (γ : EB ⟶ EB') :
    mateEquiv asys alevel (τ.whiskerBottom γ) =
      (mateEquiv asys alevel τ).whiskerLeft γ := by
  ext M
  simp only [mateEquiv, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, TwoSquare] at τ ⊢
  erw [Category.comp_id, Category.id_comp]
  have hn := γ.naturality (asys.counit.app M)
  have hh := congrArg (fun f ↦ alevel.unit.app (EA.obj (Gs.obj M)) ≫
    Gl.map (τ.app (Gs.obj M)) ≫ Gl.map f) hn
  simpa only [Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp,
    Functor.comp_obj, Functor.id_obj] using hh.symm

section Grid
universe c' cv' e' ev'
variable {C' : Type c'} [Category.{cv'} C'] {D' : Type e'} [Category.{ev'} D']
  {Fn : C' ⥤ D'} {Gn : D' ⥤ C'} (an : Fn ⊣ Gn)
  (RA : C' ⥤ C) (RB : D' ⥤ D)
  (EA₀ : A ⥤ C) (EA₁ : A ⥤ C') (EB₀ : B ⥤ D) (EB₁ : B ⥤ D')
  (α₀ : Fs ⋙ EB₀ ≅ EA₀ ⋙ Fl) (α₁ : Fs ⋙ EB₁ ≅ EA₁ ⋙ Fn)
  (δ : RA ⋙ Fl ≅ Fn ⋙ RB)
  (tA : EA₀ ⟶ EA₁ ⋙ RA) (tB : EB₀ ⟶ EB₁ ⋙ RB)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] in
private theorem transition_mates
    (ht : ∀ H, tB.app (Fs.obj H) ≫ RB.map (α₁.hom.app H) =
      α₀.hom.app H ≫ Fl.map (tA.app H) ≫ δ.hom.app (EA₁.obj H)) (M : B) :
    tA.app (Gs.obj M) ≫
      RA.map ((mateEquiv asys an (TwoSquare.mk _ _ _ _ α₁.inv)).app M) ≫
      (mateEquiv an alevel (TwoSquare.mk _ _ _ _ δ.hom)).app (EB₁.obj M) =
    (mateEquiv asys alevel (TwoSquare.mk _ _ _ _ α₀.inv)).app M ≫
      Gl.map (tB.app M) := by
  let τ₁ : TwoSquare EA₁ Fs Fn EB₁ := α₁.inv
  let τ₂ : TwoSquare RA Fn Fl RB := δ.hom
  let τ₀ : TwoSquare EA₀ Fs Fl EB₀ := α₀.inv
  have hh : (τ₁.hComp τ₂).whiskerTop tA = τ₀.whiskerBottom tB := by
    ext H
    dsimp only [τ₀, τ₁, τ₂]
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply (cancel_epi (α₀.hom.app H)).1
    apply (cancel_mono (RB.map (α₁.hom.app H))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← RB.map_comp,
      Iso.inv_hom_id_app]
    erw [RB.map_id, Category.comp_id]
    exact (ht H).symm
  have hm := congrArg (mateEquiv asys alevel) hh
  rw [mate_whiskerTop asys alevel, mate_whiskerBottom asys alevel,
    mateEquiv_vcomp asys an alevel] at hm
  have hc := congr_app hm M
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using hc

end Grid

end MateNaturality

section TensorSquare

universe c cv e ev
variable {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  (TA : A ⥤ C) (RA : C ⥤ A) (TB : B ⥤ D) (RB : D ⥤ B)
  (Fn : C ⥤ D) (Gn : D ⥤ C)
  (aTA : TA ⊣ RA) (aTB : TB ⊣ RB) (an : Fn ⊣ Gn)
  (β : RA ⋙ F ≅ Fn ⋙ RB)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem tensorSquare_exists
    [IsIso (mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom))] :
    ∃ θ : TA ⋙ Fn ≅ F ⋙ TB, ∀ M,
      F.map (aTA.unit.app M) ≫ β.hom.app (TA.obj M) ≫
        RB.map (θ.hom.app M) = aTB.unit.app (F.obj M) := by
  let τ := (mateEquiv aTA aTB).symm (TwoSquare.mk _ _ _ _ β.hom)
  have ht : (mateEquiv aTA aTB τ) = β.hom :=
    ((mateEquiv aTA aTB).apply_symm_apply _)
  have hc : conjugateEquiv (aTA.comp an) (a.comp aTB) τ =
      (mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom)) := by
    rw [← iterated_mateEquiv_conjugateEquiv aTA aTB a an τ]
    exact congrArg (fun t ↦ (mateEquiv an a t)) ht
  have : IsIso (conjugateEquiv (aTA.comp an) (a.comp aTB) τ) := by
    rw [hc]
    infer_instance
  have : IsIso τ :=
    conjugateEquiv_of_iso (aTA.comp an) (a.comp aTB) τ
  let θ := (asIso τ).symm
  refine ⟨θ, ?_⟩
  intro M
  have hu := unit_mateEquiv aTA aTB τ M
  change F.map (aTA.unit.app M) ≫
    ((mateEquiv aTA aTB τ)).app (TA.obj M) =
      aTB.unit.app (F.obj M) ≫ RB.map (τ.app M) at hu
  rw [ht] at hu
  rw [← Category.assoc, hu, Category.assoc, ← RB.map_comp]
  change aTB.unit.app (F.obj M) ≫ RB.map
    ((asIso τ).hom.app M ≫ (asIso τ).inv.app M) = _
  rw [Iso.hom_inv_id_app]
  erw [RB.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem tensorSquare_transpose (θ : TA ⋙ Fn ≅ F ⋙ TB)
    (hθ : ∀ M, F.map (aTA.unit.app M) ≫ β.hom.app (TA.obj M) ≫
      RB.map (θ.hom.app M) = aTB.unit.app (F.obj M)) (M) :
    aTB.homEquiv _ _ (θ.inv.app M) =
      F.map (aTA.unit.app M) ≫ β.hom.app (TA.obj M) := by
  rw [Adjunction.homEquiv_unit]
  apply (cancel_mono (RB.map (θ.hom.app M))).1
  rw [Category.assoc, ← RB.map_comp, Iso.inv_hom_id_app]
  erw [RB.map_id, Category.comp_id]
  simpa only [Category.assoc] using (hθ M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem fourMate_isIso
    (hτ : IsIso ((mateEquiv aTA aTB).symm (TwoSquare.mk _ _ _ _ β.hom))) :
    IsIso (mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom)) := by
  have := hτ
  let τ := (mateEquiv aTA aTB).symm (TwoSquare.mk _ _ _ _ β.hom)
  have ht : (mateEquiv aTA aTB τ) = β.hom :=
    ((mateEquiv aTA aTB).apply_symm_apply _)
  have hc : conjugateEquiv (aTA.comp an) (a.comp aTB) τ =
      (mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom)) := by
    rw [← iterated_mateEquiv_conjugateEquiv aTA aTB a an τ]
    exact congrArg (fun t ↦ (mateEquiv an a t)) ht
  rw [← hc]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem doubleMate_homEquiv (M : A) (N : D)
    (f : Fn.obj (TA.obj M) ⟶ N) :
    aTA.homEquiv _ _ (an.homEquiv _ _ f) ≫
      (mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom)).app N =
    a.homEquiv _ _ (aTB.homEquiv _ _
      (((mateEquiv aTA aTB).symm (TwoSquare.mk _ _ _ _ β.hom)).app M ≫ f)) := by
  let τ := (mateEquiv aTA aTB).symm (TwoSquare.mk _ _ _ _ β.hom)
  have ht : (mateEquiv aTA aTB τ) = β.hom :=
    ((mateEquiv aTA aTB).apply_symm_apply _)
  have hc : conjugateEquiv (aTA.comp an) (a.comp aTB) τ =
      (mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom)) := by
    rw [← iterated_mateEquiv_conjugateEquiv aTA aTB a an τ]
    exact congrArg (fun t ↦ (mateEquiv an a t)) ht
  change _ ≫ ((mateEquiv an a (TwoSquare.mk _ _ _ _ β.hom))).app N = _
  rw [← hc]
  have h₁ : (aTA.comp an).homEquiv M N f =
      aTA.homEquiv M _ (an.homEquiv _ N f) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  have h₂ : (a.comp aTB).homEquiv M N (τ.app M ≫ f) =
      a.homEquiv M _ (aTB.homEquiv _ N (τ.app M ≫ f)) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  change _ = a.homEquiv _ _ (aTB.homEquiv _ _ (τ.app M ≫ f))
  rw [← h₁, ← h₂, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Category.assoc]
  erw [(conjugateEquiv (aTA.comp an) (a.comp aTB) τ).naturality f]
  erw [← Category.assoc, unit_conjugateEquiv, Category.assoc, ← Functor.map_comp]

end TensorSquare

section DerivedLeftSquare

universe c cv e ev
variable {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type e} [Category.{ev} D] [Abelian D] [HasDerivedCategory.{d} D]
  (TA : A ⥤ C) (RA : C ⥤ A) (TB : B ⥤ D) (RB : D ⥤ B)
  [TA.Additive] [RA.Additive] [TB.Additive] [RB.Additive]
  (aTA : TA ⊣ RA) (aTB : TB ⊣ RB)
  (pA : CochainComplex A ℤ → Prop) (pB : CochainComplex B ℤ → Prop)
  (DA : DerivedCoefficientScalarExtension TA RA aTA pA)
  (DB : DerivedCoefficientScalarExtension TB RB aTB pB)
  (Fn : C ⥤ D) [Fn.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (FnD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φn : DerivedCategory.Q ⋙ FnD ≅ Fn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (β : RA ⋙ F ≅ Fn ⋙ RB)
  (βD : DA.restriction ⋙ FD ≅ FnD ⋙ DB.restriction)
  (hβD : ∀ K,
    βD.hom.app (DerivedCategory.Q.obj K) ≫
      DB.restriction.map (φn.hom.app K) ≫
      DB.restrictionFactors.hom.app ((Fn.mapHomologicalComplex (.up ℤ)).obj K) =
    FD.map (DA.restrictionFactors.hom.app K) ≫
      φF.hom.app ((RA.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app K))
  (ι : F ⋙ TB ≅ TA ⋙ Fn)
  (hι : ∀ P, aTB.homEquiv _ _ (ι.hom.app P) =
    F.map (aTA.unit.app P) ≫ β.hom.app (TA.obj P))

private def derivedLeftSquare : FD ⋙ DB.derived ⟶ DA.derived ⋙ FnD :=
  ((mateEquiv DA.derivedAdj DB.derivedAdj).symm (TwoSquare.mk _ _ _ _ βD.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hβD hι in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem derivedLeftSquare_rep (P : CochainComplex A ℤ) :
    (derivedLeftSquare TA RA TB RB aTA aTB pA pB DA DB FD FnD βD).app (DerivedCategory.Q.obj P) ≫
      FnD.map (DA.counit.app P) ≫
      φn.hom.app ((TA.mapHomologicalComplex (.up ℤ)).obj P) =
    DB.derived.map (φF.hom.app P) ≫
      DB.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ι (.up ℤ)).hom.app P) := by
  apply derivedMate_comparison
    (aTA.mapHomologicalComplex (.up ℤ)) (aTB.mapHomologicalComplex (.up ℤ))
    DA.derivedAdj DB.derivedAdj DA.counit DB.counit DA.restrictionFactors
    DB.restrictionFactors φF φn DA.transpose DB.transpose
    (TwoSquare.mk _ _ _ _ ((NatIso.mapHomologicalComplex β (.up ℤ)).hom))
    (TwoSquare.mk _ _ _ _ βD.hom) hβD
    (NatIso.mapHomologicalComplex ι (.up ℤ)).hom ?_ P
  intro P
  ext i
  exact hι (P.X i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include Fn φF φn β hβD ι hι in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem derivedLeftSquare_isIso
    (res : CochainComplex A ℤ → Prop)
    (hres : ∀ K, ∃ (P : CochainComplex A ℤ) (q : P ⟶ K), QuasiIso q ∧ res P)
    (hcA : ∀ P, res P → IsIso (DA.counit.app P))
    (hcB : ∀ P, res P → IsIso
      (DB.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    IsIso (derivedLeftSquare TA RA TB RB aTA aTB pA pB DA DB FD FnD βD) := by
  let τ := derivedLeftSquare TA RA TB RB aTA aTB pA pB DA DB FD FnD βD
  have hi P (hP : res P) : IsIso (τ.app (DerivedCategory.Q.obj P)) := by
    have := hcA P hP
    have := hcB P hP
    have h := derivedLeftSquare_rep F TA RA TB RB aTA aTB pA pB DA DB Fn FD FnD
      φF φn β βD hβD ι hι P
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ FnD.map (DA.counit.app P) ≫
        φn.hom.app ((TA.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [show τ.app _ ≫ _ ≫ _ = _ from h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (FnD.map (DA.counit.app P) ≫
        φn.hom.app ((TA.mapHomologicalComplex (.up ℤ)).obj P))
  have (X : DerivedCategory A) : IsIso (τ.app X) := by
    obtain ⟨P, q, hq, hP⟩ := hres (DerivedCategory.Q.objPreimage X)
    have := hq
    have := hi P hP
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    exact (NatTrans.isIso_app_iff_of_iso τ e).1 inferInstance
  exact NatIso.isIso_of_isIso_app τ

end DerivedLeftSquare

end Abstract

section TransitionLocalization

universe a av b bv cn cnv cm cmv dn dnv dm dmv
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {Cn : Type cn} [Category.{cnv} Cn] [Abelian Cn] [HasDerivedCategory.{d} Cn]
  {Cm : Type cm} [Category.{cmv} Cm] [Abelian Cm] [HasDerivedCategory.{d} Cm]
  {Dn : Type dn} [Category.{dnv} Dn] [Abelian Dn] [HasDerivedCategory.{d} Dn]
  {Dm : Type dm} [Category.{dmv} Dm] [Abelian Dm] [HasDerivedCategory.{d} Dm]
  (F : A ⥤ B) (eAn : A ⥤ Cn) (eAm : A ⥤ Cm)
  (eBn : B ⥤ Dn) (eBm : B ⥤ Dm) (Fn : Cn ⥤ Dn) (Fm : Cm ⥤ Dm)
  (RA : Cn ⥤ Cm) (RB : Dn ⥤ Dm)
  [F.Additive] [eAn.Additive] [eAm.Additive] [eBn.Additive] [eBm.Additive]
  [Fn.Additive] [Fm.Additive] [RA.Additive] [RB.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (AnD : DerivedCategory A ⥤ DerivedCategory Cn)
  (AmD : DerivedCategory A ⥤ DerivedCategory Cm)
  (BnD : DerivedCategory B ⥤ DerivedCategory Dn)
  (BmD : DerivedCategory B ⥤ DerivedCategory Dm)
  (FnD : DerivedCategory Cn ⥤ DerivedCategory Dn)
  (FmD : DerivedCategory Cm ⥤ DerivedCategory Dm)
  (RAD : DerivedCategory Cn ⥤ DerivedCategory Cm)
  (RBD : DerivedCategory Dn ⥤ DerivedCategory Dm)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φAn : DerivedCategory.Q ⋙ AnD ≅ eAn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φAm : DerivedCategory.Q ⋙ AmD ≅ eAm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φBn : DerivedCategory.Q ⋙ BnD ≅ eBn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φBm : DerivedCategory.Q ⋙ BmD ≅ eBm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φFn : DerivedCategory.Q ⋙ FnD ≅ Fn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φFm : DerivedCategory.Q ⋙ FmD ≅ Fm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φRA : DerivedCategory.Q ⋙ RAD ≅ RA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φRB : DerivedCategory.Q ⋙ RBD ≅ RB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (αn : F ⋙ eBn ≅ eAn ⋙ Fn) (αm : F ⋙ eBm ≅ eAm ⋙ Fm)
  (β : RA ⋙ Fm ≅ Fn ⋙ RB)
  (αnD : FD ⋙ BnD ≅ AnD ⋙ FnD) (αmD : FD ⋙ BmD ≅ AmD ⋙ FmD)
  (βD : RAD ⋙ FmD ≅ FnD ⋙ RBD)
  (tA : eAm ⟶ eAn ⋙ RA) (tB : eBm ⟶ eBn ⋙ RB)
  (tAD : AmD ⟶ AnD ⋙ RAD) (tBD : BmD ⟶ BnD ⋙ RBD)
  (hαn : ∀ P, αnD.hom.app (DerivedCategory.Q.obj P) ≫
    FnD.map (φAn.hom.app P) ≫ φFn.hom.app ((eAn.mapHomologicalComplex (.up ℤ)).obj P) =
    BnD.map (φF.hom.app P) ≫ φBn.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex αn (.up ℤ)).hom.app P))
  (hαm : ∀ P, αmD.hom.app (DerivedCategory.Q.obj P) ≫
    FmD.map (φAm.hom.app P) ≫ φFm.hom.app ((eAm.mapHomologicalComplex (.up ℤ)).obj P) =
    BmD.map (φF.hom.app P) ≫ φBm.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex αm (.up ℤ)).hom.app P))
  (hβD : ∀ P, βD.hom.app (DerivedCategory.Q.obj P) ≫
    RBD.map (φFn.hom.app P) ≫ φRB.hom.app ((Fn.mapHomologicalComplex (.up ℤ)).obj P) =
    FmD.map (φRA.hom.app P) ≫ φFm.hom.app ((RA.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P))
  (htA : ∀ P, tAD.app (DerivedCategory.Q.obj P) ≫ RAD.map (φAn.hom.app P) ≫
    φRA.hom.app ((eAn.mapHomologicalComplex (.up ℤ)).obj P) =
    φAm.hom.app P ≫ DerivedCategory.Q.map ((tA.mapHomologicalComplex (.up ℤ)).app P))
  (htB : ∀ P, tBD.app (DerivedCategory.Q.obj P) ≫ RBD.map (φBn.hom.app P) ≫
    φRB.hom.app ((eBn.mapHomologicalComplex (.up ℤ)).obj P) =
    φBm.hom.app P ≫ DerivedCategory.Q.map ((tB.mapHomologicalComplex (.up ℤ)).app P))
  (ho : ∀ M, tB.app (F.obj M) ≫ RB.map (αn.hom.app M) =
    αm.hom.app M ≫ Fm.map (tA.app M) ≫ β.hom.app (eAn.obj M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hαn hαm hβD htA htB ho in
private theorem transition_localization (H : DerivedCategory A) :
    tBD.app (FD.obj H) ≫ RBD.map (αnD.hom.app H) =
    αmD.hom.app H ≫ FmD.map (tAD.app H) ≫ βD.hom.app (AnD.obj H) := by
  let t₁ := whiskerLeft FD tBD ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight αnD.hom RBD ≫
    (Functor.associator _ _ _).hom
  let t₂ := αmD.hom ≫
    whiskerRight tAD FmD ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft AnD βD.hom
  suffices ht : t₁ = t₂ by
    simpa only [t₁, t₂, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using congr_app ht H
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (DerivedCategory Dm)).map_injective
  apply NatTrans.ext
  funext P
  dsimp only [whiskeringLeft, t₁, t₂, whiskerLeft_app, whiskerRight_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]
  change tBD.app (FD.obj (DerivedCategory.Q.obj P)) ≫
      RBD.map
        (αnD.hom.app (DerivedCategory.Q.obj P)) =
    αmD.hom.app (DerivedCategory.Q.obj P) ≫
      FmD.map (tAD.app (DerivedCategory.Q.obj P)) ≫
      βD.hom.app (AnD.obj (DerivedCategory.Q.obj P))
  apply (cancel_mono (RBD.map
    (FnD.map (φAn.hom.app P)) ≫
    RBD.map (φFn.hom.app
      ((eAn.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    φRB.hom.app
      ((Fn.mapHomologicalComplex (.up ℤ)).obj
        ((eAn.mapHomologicalComplex (.up ℤ)).obj P)))).1
  have hn := hαn P
  have hm := hαm P
  have htX := htB ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have htY := htA P
  have hd := hβD ((eAn.mapHomologicalComplex (.up ℤ)).obj P)
  have hnr := congrArg RBD.map hn
  simp only [Functor.map_comp] at hnr
  simp only [Category.assoc]
  rw [reassoc_of% hnr]
  have nr := φRB.hom.naturality
    ((Functor.mapHomologicalComplexCompIso αn (.up ℤ)).hom.app P)
  dsimp only [Functor.comp_map] at nr
  slice_lhs 4 5 => exact nr
  have nt := tBD.naturality (φF.hom.app P)
  dsimp only [Functor.comp_map] at nt
  erw [← reassoc_of% nt, reassoc_of% htX]
  have nd := βD.hom.naturality (φAn.hom.app P)
  dsimp only [Functor.comp_map] at nd
  erw [← reassoc_of% nd]
  slice_rhs 4 6 => exact hd
  have htyr := congrArg FmD.map htY
  simp only [Functor.map_comp] at htyr
  slice_rhs 2 4 => exact htyr
  have nf := φFm.hom.naturality
    ((tA.mapHomologicalComplex (.up ℤ)).app P)
  dsimp only [Functor.comp_map] at nf
  slice_rhs 3 4 => exact nf
  slice_rhs 1 3 => exact hm
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
  congr 1
  congr 1
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.hom_ext
  intro i
  exact ho (P.X i)

end TransitionLocalization

section OrdinaryRestriction

universe a₀v a₁v b₀v b₁v xv yv a₀u a₁u b₀u b₁u xu yu
variable {A₀ : Type a₀u} [Category.{a₀v} A₀] {A₁ : Type a₁u} [Category.{a₁v} A₁]
  {B₀ : Type b₀u} [Category.{b₀v} B₀] {B₁ : Type b₁u} [Category.{b₁v} B₁]
  {X : Type xu} [Category.{xv} X] {Y : Type yu} [Category.{yv} Y]
  (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀) (a₀ : F₀ ⊣ G₀)
  (F₁ : A₁ ⥤ B₁) (G₁ : B₁ ⥤ A₁) (a₁ : F₁ ⊣ G₁)
  (RA : A₀ ⥤ A₁) (RB : B₀ ⥤ B₁)
  (Ua : A₁ ⥤ X) (Un : A₀ ⥤ X) (Ub : B₁ ⥤ Y) (Uq : B₀ ⥤ Y)
  [Ua.ReflectsIsomorphisms]
  (L : X ⥤ Y) (V : Y ⥤ X) (adj : L ⊣ V)
  (ra : RA ⋙ Ua ≅ Un) (rb : RB ⋙ Ub ≅ Uq)
  (mu₀ : F₀ ⋙ Uq ≅ Un ⋙ L) (mu₁ : F₁ ⋙ Ub ≅ Ua ⋙ L)
  (γ₀ : G₀ ⋙ Un ≅ Uq ⋙ V) (γ₁ : G₁ ⋙ Ua ≅ Ub ⋙ V)
  (β : RA ⋙ F₁ ≅ F₀ ⋙ RB)
  (h₀ : ∀ M N (f : F₀.obj M ⟶ N),
    Un.map (a₀.homEquiv M N f) ≫ γ₀.hom.app N =
      adj.homEquiv _ _ (mu₀.inv.app M ≫ Uq.map f))
  (h₁ : ∀ M N (f : F₁.obj M ⟶ N),
    Ua.map (a₁.homEquiv M N f) ≫ γ₁.hom.app N =
      adj.homEquiv _ _ (mu₁.inv.app M ≫ Ub.map f))
  (hβ : ∀ M, Ub.map (β.hom.app M) ≫ rb.hom.app (F₀.obj M) ≫ mu₀.hom.app M =
    mu₁.hom.app (RA.obj M) ≫ L.map (ra.hom.app M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include h₀ h₁ hβ in
private theorem restrictionMate_isIso :
    IsIso (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)) := by
  let α := (mateEquiv a₀ a₁
    (TwoSquare.mk _ _ _ _ β.hom))
  have hα (N) : Ua.map (α.app N) ≫ γ₁.hom.app (RB.obj N) ≫
      V.map (rb.hom.app N) = ra.hom.app (G₀.obj N) ≫
        γ₀.hom.app N := by
    let M := G₀.obj N
    let ε := a₀.counit.app N
    have ha : α.app N = a₁.homEquiv _ _
        (β.hom.app M ≫ RB.map ε) := by
      dsimp only [α, mateEquiv, TwoSquare.mk,
        Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
        Functor.leftUnitor_hom_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.comp_obj]
      simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.id_comp]
      dsimp only [Functor.comp_map]
      erw [Category.comp_id]
    rw [ha]
    erw [← Category.assoc, h₁]
    rw [← adj.homEquiv_naturality_right]
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    have hb := rb.hom.naturality ε
    change Ub.map (RB.map ε) ≫ rb.hom.app N =
      rb.hom.app (F₀.obj M) ≫ Uq.map ε at hb
    simp only [Functor.map_comp, Category.assoc]
    rw [hb]
    have hi := hβ M
    have hi' : mu₁.inv.app (RA.obj M) ≫
        Ub.map (β.hom.app M) ≫
        rb.hom.app (F₀.obj M) =
      L.map (ra.hom.app M) ≫ mu₀.inv.app M := by
      apply (cancel_epi (mu₁.hom.app (RA.obj M))).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      apply (cancel_mono (mu₀.hom.app M)).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact hi
    dsimp only [Functor.comp_obj]
    slice_lhs 1 3 => exact hi'
    rw [Category.assoc]
    rw [Adjunction.homEquiv_naturality_left_symm]
    have hε : a₀.homEquiv M N ε = 𝟙 M := by
      rw [Adjunction.homEquiv_unit, a₀.right_triangle_components]
    have hn := h₀ M N ε
    rw [hε] at hn
    erw [Un.map_id M, Category.id_comp] at hn
    erw [hn, Equiv.symm_apply_apply]
  have hi (N) : IsIso (α.app N) := by
    have : IsIso (Ua.map (α.app N) ≫
        γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N)) := by
      rw [hα]
      infer_instance
    have : IsIso (Ua.map (α.app N)) := IsIso.of_isIso_comp_right _
      (γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N))
    exact isIso_of_reflects_iso (α.app N) Ua
  exact NatIso.isIso_of_isIso_app α

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hβ in
private theorem transition_bridge [Ub.Faithful]
    (M₀ : A₀) (M₁ : A₁) (N₀ : B₀) (N₁ : B₁)
    (a₀ : N₀ ⟶ F₀.obj M₀) (a₁ : N₁ ⟶ F₁.obj M₁)
    (t : N₁ ⟶ RB.obj N₀) (r : M₁ ⟶ RA.obj M₀) :
    t ≫ RB.map a₀ = a₁ ≫ F₁.map r ≫ β.hom.app M₀ ↔
      (Ub.map t ≫ rb.hom.app N₀) ≫ Uq.map a₀ ≫ mu₀.hom.app M₀ =
        (Ub.map a₁ ≫ mu₁.hom.app M₁) ≫ L.map (Ua.map r ≫ ra.hom.app M₀) := by
  let c := rb.hom.app (F₀.obj M₀) ≫ mu₀.hom.app M₀
  rw [← Ub.map_injective.eq_iff, ← cancel_mono c]
  dsimp only [c]
  simp only [Functor.map_comp, Category.assoc]
  have hn := rb.hom.naturality a₀
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hm := mu₁.hom.naturality r
  dsimp only [Functor.comp_map, Functor.comp_obj] at hm
  have hn' := congrArg (fun f ↦ Ub.map t ≫ f ≫ mu₀.hom.app M₀) hn
  have hb' := congrArg (fun f ↦ Ub.map a₁ ≫ Ub.map (F₁.map r) ≫ f) (hβ M₀)
  have hm' := congrArg (fun f ↦ Ub.map a₁ ≫ f ≫ L.map (ra.hom.app M₀)) hm
  simp only [Category.assoc] at hn' hb' hm'
  rw [hn', hb', hm']

end OrdinaryRestriction

section Assembly

universe a av b bv c cv e ev
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {MA : ℕ → Type c} [∀ n, Category.{cv} (MA n)] [∀ n, Abelian (MA n)]
  [∀ n, HasDerivedCategory.{d} (MA n)]
  {MB : ℕ → Type e} [∀ n, Category.{ev} (MB n)] [∀ n, Abelian (MB n)]
  [∀ n, HasDerivedCategory.{d} (MB n)]
  {eA : ∀ n, A ⥤ MA n} [∀ n, (eA n).Additive]
  {eB : ∀ n, B ⥤ MB n} [∀ n, (eB n).Additive]
  {RA : ∀ {m n : ℕ}, n ≤ m → MA n ⥤ MA m} [∀ m n (h : n ≤ m), (RA h).Additive]
  {RB : ∀ {m n : ℕ}, n ≤ m → MB n ⥤ MB m} [∀ m n (h : n ≤ m), (RB h).Additive]
  {TA : ∀ {m n : ℕ}, n ≤ m → MA m ⥤ MA n} [∀ m n (h : n ≤ m), (TA h).Additive]
  {TB : ∀ {m n : ℕ}, n ≤ m → MB m ⥤ MB n} [∀ m n (h : n ≤ m), (TB h).Additive]
  {atA : ∀ {m n : ℕ} (h : n ≤ m), TA h ⊣ RA h}
  {atB : ∀ {m n : ℕ} (h : n ≤ m), TB h ⊣ RB h}
  {KFA : ∀ n, CochainComplex (MA n) ℤ → Prop} {FlatA : ∀ n, MA n → Prop}
  {KFB : ∀ n, CochainComplex (MB n) ℤ → Prop} {FlatB : ∀ n, MB n → Prop}
  {TN₁ : (∀ {m n : ℕ} (h : n ≤ m), eA m ⟶ eA n ⋙ RA h) → Prop}
  {TN₂ : (∀ {m n : ℕ} (h : n ≤ m), eB m ⟶ eB n ⋙ RB h) → Prop}
  {UN₁ : (∀ n, TA (Nat.le_refl n) ≅ 𝟭 (MA n)) → Prop}
  {UN₂ : (∀ n, TB (Nat.le_refl n) ≅ 𝟭 (MB n)) → Prop}
  {AN₁ : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    TA h₁ ⋙ TA h₂ ≅ TA (h₂.trans h₁)) → Prop}
  {AN₂ : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    TB h₁ ⋙ TB h₂ ≅ TB (h₂.trans h₁)) → Prop}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def extensionPairAbstract
    (P : CoefficientEvaluationExtensionData eA RA TA atA KFA FlatA TN₁ UN₁ AN₁) (n : ℕ) :
    DerivedCoefficientScalarExtension (P.extension n) (eA n)
      (P.adj n) (fun K ↦ KFA n K ∧ ∀ i : ℤ, FlatA n (K.X i)) :=
  { derived := P.derivedExtension n
    counit := P.counit n
    isDerived := P.isDerived n
    computes := fun K hK ↦ P.computes n K hK.1 hK.2
    restriction := P.evaluation n
    restrictionFactors := P.evaluationFactors n
    derivedAdj := P.derivedAdj n
    transpose := P.transpose n }

variable (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (a : F ⊣ G)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Fl : ∀ n, MA n ⥤ MB n) (Gl : ∀ n, MB n ⥤ MA n)
  [∀ n, (Fl n).Additive] [∀ n, (Gl n).Additive] (al : ∀ n, Fl n ⊣ Gl n)
  (PY : CoefficientEvaluationExtensionData eA RA TA atA KFA FlatA TN₁ UN₁ AN₁)
  (PX : CoefficientEvaluationExtensionData eB RB TB atB KFB FlatB TN₂ UN₂ AN₂)
  (α : ∀ n, F ⋙ eB n ≅ eA n ⋙ Fl n)
  (β : ∀ {m n : ℕ} (h : n ≤ m), RA h ⋙ Fl m ≅ Fl n ⋙ RB h)
  (ds : CoefficientDerivedImage F G a)
  (dl : ∀ n, CoefficientDerivedImage (Fl n) (Gl n) (al n))
  (hr : ∀ n (K : CochainComplex (MA n) ℤ),
    ∃ (P : CochainComplex (MA n) ℤ) (q : P ⟶ K), QuasiIso q ∧ KFA n P ∧
      (∀ i : ℤ, FlatA n (P.X i)) ∧ KFB n (((Fl n).mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, FlatB n ((Fl n).obj (P.X i)))
  (hRestr : ∀ {m n : ℕ} (h : n ≤ m),
    IsIso (mateEquiv (al n) (al m) (TwoSquare.mk _ _ _ _ (β h).hom)))
  (hEval : ∀ n,
    IsIso (mateEquiv a (al n) (TwoSquare.mk _ _ _ _ (α n).inv)))
  (hTrans : ∀ {m n : ℕ} (h : n ≤ m) M,
    (PX.strictTransition h).app (F.obj M) ≫ (RB h).map ((α n).hom.app M) =
    (α m).hom.app M ≫ (Fl m).map ((PY.strictTransition h).app M) ≫
      (β h).hom.app ((eA n).obj M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include ds dl hr hRestr hEval hTrans in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem comparison_assembly :
    ∃ E : CoefficientEvaluationImageData F G a Fl Gl al eA eB
      PY.evaluation PX.evaluation PY.evaluationFactors PX.evaluationFactors α,
    Nonempty (CoefficientScalarImageData (F := F) (G := G) (adj := a)
      (Flevel := Fl) (Glevel := Gl) (adjLevel := al) (eA := eA) (eB := eB)
      (EA := PY.evaluation) (EB := PX.evaluation)
      (factorsA := PY.evaluationFactors) (factorsB := PX.evaluationFactors) (alpha := α)
      (fun {_ _} h ↦ TA h) (fun {_ _} h ↦ RA h) (fun {_ _} h ↦ atA h) KFA FlatA
      (fun {_ _} h ↦ PY.scalar h) (fun {_ _} h ↦ TB h) (fun {_ _} h ↦ RB h)
      (fun {_ _} h ↦ atB h) KFB (fun {_ _} h ↦ PX.scalar h)
      (fun {_ _} h ↦ PY.transition h) (fun {_ _} h ↦ PX.transition h) β E) := by
  have he (n : ℕ) := derivedSquare_exists F
    (eA n)
    (eB n) (Fl n)
    ds.inverse (PY.evaluation n) (PX.evaluation n) (dl n).inverse
    ds.inverseFactors (PY.evaluationFactors n) (PX.evaluationFactors n)
    (dl n).inverseFactors (α n)
  have hb {m n : ℕ} (h : n ≤ m) := derivedSquare_exists
    (RA h)
    (Fl n) (Fl m) (RB h)
    (PY.scalar h).restriction (dl n).inverse (dl m).inverse (PX.scalar h).restriction
    (PY.scalar h).restrictionFactors (dl n).inverseFactors
    (dl m).inverseFactors (PX.scalar h).restrictionFactors (β h)
  have ht {m n : ℕ} (h : n ≤ m) : ∃ θ :
      TA h ⋙ (Fl n) ≅
        (Fl m) ⋙ TB h,
      ∀ M, (Fl m).map ((atA h).unit.app M) ≫
        (β h).hom.app ((TA h).obj M) ≫
        (RB h).map (θ.hom.app M) =
          (atB h).unit.app ((Fl m).obj M) := by
    have := hRestr h
    exact tensorSquare_exists (Fl m) (Gl m) (al m)
      (TA h) (RA h)
      (TB h) (RB h)
      (Fl n) (Gl n) (atA h)
      (atB h) (al n) (β h)
  choose δ hδ using @hb
  choose θ hθ using @ht
  have heo (n : ℕ) : ∃ χ : PY.extension n ⋙ F ≅
      (Fl n) ⋙ PX.extension n,
      ∀ M, (Fl n).map ((PY.adj n).unit.app M) ≫
        (α n).inv.app ((PY.extension n).obj M) ≫
        (eB n).map (χ.hom.app M) =
          (PX.adj n).unit.app ((Fl n).obj M) := by
    have : IsIso (mateEquiv a (al n)
        (TwoSquare.mk _ _ _ _ (α n).symm.hom)) := hEval n
    exact tensorSquare_exists (Fl n) (Gl n) (al n)
      (PY.extension n) (eA n)
      (PX.extension n) (eB n)
      F G (PY.adj n) (PX.adj n) a
      (α n).symm
  have hdT {m n : ℕ} (h : n ≤ m) : IsIso
      (derivedLeftSquare
        (TA h) (RA h)
        (TB h) (RB h)
        (atA h) (atB h)
        _ _ (PY.scalar h) (PX.scalar h) (dl m).inverse (dl n).inverse (δ h)) := by
    apply derivedLeftSquare_isIso (Fl m)
      (TA h) (RA h)
      (TB h) (RB h)
      (atA h) (atB h)
      _ _ (PY.scalar h) (PX.scalar h) (Fl n)
      (dl m).inverse (dl n).inverse (dl m).inverseFactors (dl n).inverseFactors
      (β h) (δ h) (hδ h) (θ h).symm
      (tensorSquare_transpose (Fl m)
        (TA h) (RA h)
        (TB h) (RB h)
        (Fl n) (atA h)
        (atB h) (β h) (θ h) (hθ h))
      (fun P ↦ KFA _ P ∧
        KFB m (((Fl m).mapHomologicalComplex (.up ℤ)).obj P))
    · intro K
      obtain ⟨P, q, hq, hp, hf, hfp, _⟩ := hr m K
      exact ⟨P, q, hq, hp, hfp⟩
    · intro P hP
      exact (PY.scalar h).computes P hP.1
    · intro P hP
      exact (PX.scalar h).computes _ hP.2
  choose ev hev using he
  choose χ hχ using heo
  have hdE (n : ℕ) : IsIso
      (derivedLeftSquare (PY.extension n) (eA n)
        (PX.extension n) (eB n) (PY.adj n) (PX.adj n)
        _ _ (extensionPairAbstract PY n) (extensionPairAbstract PX n)
        (dl n).inverse ds.inverse (ev n).symm) := by
    apply derivedLeftSquare_isIso (Fl n)
      (PY.extension n) (eA n)
      (PX.extension n) (eB n) (PY.adj n) (PX.adj n)
      _ _ (extensionPairAbstract PY n) (extensionPairAbstract PX n)
      F (dl n).inverse ds.inverse (dl n).inverseFactors ds.inverseFactors
      (α n).symm (ev n).symm
      (derivedSquare_symm_rep F
        (eA n) (eB n)
        (Fl n) ds.inverse (PY.evaluation n) (PX.evaluation n) (dl n).inverse
        ds.inverseFactors (PY.evaluationFactors n) (PX.evaluationFactors n)
        (dl n).inverseFactors (α n) (ev n) (hev n))
      (χ n).symm
      (tensorSquare_transpose (Fl n) (PY.extension n)
        (eA n) (PX.extension n)
        (eB n) F (PY.adj n) (PX.adj n)
        (α n).symm (χ n) (hχ n))
      (fun P ↦ (KFA _ P ∧
        ∀ i : ℤ, FlatA n (P.X i)) ∧
        (KFB n (((Fl n).mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, FlatB n ((Fl n).obj (P.X i))))
    · intro K
      obtain ⟨P, q, hq, hp, hf, hfp, hff⟩ := hr n K
      exact ⟨P, q, hq, ⟨hp, hf⟩, hfp, hff⟩
    · intro P hP
      exact PY.computes n P hP.1.1 hP.1.2
    · intro P hP
      exact PX.computes n _ hP.2.1 hP.2.2
  have hdEv (n : ℕ) : IsIso (mateEquiv ds.adjunction (dl n).adjunction
      (TwoSquare.mk _ _ _ _ (ev n).inv)) := by
    have := hdE n
    exact fourMate_isIso (dl n).inverse (dl n).direct (dl n).adjunction
      (PY.derivedExtension n) (PY.evaluation n) (PX.derivedExtension n) (PX.evaluation n)
      ds.inverse ds.direct (PY.derivedAdj n) (PX.derivedAdj n) ds.adjunction (ev n).symm (hdE n)
  let de := fun n ↦ (asIso
    (mateEquiv ds.adjunction (dl n).adjunction
      (TwoSquare.mk _ _ _ _ (ev n).inv)))
  let E : CoefficientEvaluationImageData F G a Fl Gl al eA eB
      PY.evaluation PX.evaluation PY.evaluationFactors PX.evaluationFactors α :=
    { system := ds
      level := dl
      inverseEvaluation := ev
      inverseEvaluation_rep := hev
      directEvaluation := de
      counit := fun n M ↦ evaluation_counit_of_mate ds.adjunction (dl n).adjunction
        (ev n) M }
  have hit {m n : ℕ} (h : n ≤ m) (H : DerivedCategory A) :
      (PX.transition h).app (E.system.inverse.obj H) ≫
        (PX.scalar h).restriction.map ((E.inverseEvaluation n).hom.app H) =
      (E.inverseEvaluation m).hom.app H ≫
        (E.level m).inverse.map ((PY.transition h).app H) ≫
        (δ h).hom.app ((PY.evaluation n).obj H) := by
    exact transition_localization F (eA n) (eA m) (eB n) (eB m) (Fl n) (Fl m)
      (RA h) (RB h) E.system.inverse (PY.evaluation n) (PY.evaluation m)
      (PX.evaluation n) (PX.evaluation m) (E.level n).inverse (E.level m).inverse
      (PY.scalar h).restriction (PX.scalar h).restriction E.system.inverseFactors
      (PY.evaluationFactors n) (PY.evaluationFactors m)
      (PX.evaluationFactors n) (PX.evaluationFactors m)
      (E.level n).inverseFactors (E.level m).inverseFactors
      (PY.scalar h).restrictionFactors (PX.scalar h).restrictionFactors
      (α n) (α m) (β h) (E.inverseEvaluation n) (E.inverseEvaluation m) (δ h)
      (PY.strictTransition h) (PX.strictTransition h) (PY.transition h) (PX.transition h)
      (E.inverseEvaluation_rep n) (E.inverseEvaluation_rep m) (hδ h)
      (PY.transition_rep h) (PX.transition_rep h) (hTrans h) H
  have hdR {m n : ℕ} (h : n ≤ m) : IsIso
      (mateEquiv (dl n).adjunction (dl m).adjunction
        (TwoSquare.mk _ _ _ _ (δ h).hom)) := by
    have := hdT h
    exact fourMate_isIso (dl m).inverse (dl m).direct (dl m).adjunction
      (PY.scalar h).derived (PY.scalar h).restriction
      (PX.scalar h).derived (PX.scalar h).restriction
      (dl n).inverse (dl n).direct (PY.scalar h).derivedAdj (PX.scalar h).derivedAdj
      (dl n).adjunction (δ h) (hdT h)
  let dt := fun {m n : ℕ} (h : n ≤ m) ↦ (asIso
    (derivedLeftSquare
      (TA h) (RA h)
      (TB h) (RB h)
      (atA h) (atB h)
      _ _ (PY.scalar h) (PX.scalar h) (dl m).inverse (dl n).inverse (δ h))).symm
  let rd := fun {m n : ℕ} (h : n ≤ m) ↦ (asIso
    (mateEquiv (dl n).adjunction (dl m).adjunction
      (TwoSquare.mk _ _ _ _ (δ h).hom))).symm
  refine ⟨E, ⟨{
    tensor := θ
    tensor_unit := hθ
    derivedTensor := dt
    derivedTensor_rep := ?_
    restrictedDirect := rd
    restrictedDirect_mate := ?_
    restrictedInverse := δ
    restrictedInverse_mate := ?_
    inverseTransition := ?_
    directTransition := ?_ }⟩⟩
  · intro m n h P _ _
    apply (cancel_epi ((dt h).inv.app (DerivedCategory.Q.obj P))).1
    simp only [Iso.inv_hom_id_app_assoc]
    have hh := derivedLeftSquare_rep (Fl m)
      (TA h) (RA h)
      (TB h) (RB h)
      (atA h) (atB h)
      _ _ (PY.scalar h) (PX.scalar h) (Fl n)
      (dl m).inverse (dl n).inverse (dl m).inverseFactors (dl n).inverseFactors
      (β h) (δ h) (hδ h) (θ h).symm
      (tensorSquare_transpose (Fl m)
        (TA h) (RA h)
        (TB h) (RB h)
        (Fl n) (atA h)
        (atB h) (β h) (θ h) (hθ h)) P
    change _ = _ ≫ (_ ≫ _ ≫ _)
    slice_rhs 1 3 => exact hh
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
    rw [show (NatIso.mapHomologicalComplex (θ h).symm (.up ℤ)).hom.app P ≫
      (NatIso.mapHomologicalComplex (θ h) (.up ℤ)).hom.app P = 𝟙 _ from
        (NatIso.mapHomologicalComplex (θ h) (.up ℤ)).inv_hom_id_app P]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  · intro m n h A B f
    apply (cancel_mono ((rd h).inv.app B)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    exact doubleMate_homEquiv (dl m).inverse (dl m).direct (dl m).adjunction
      (PY.scalar h).derived (PY.scalar h).restriction
      (PX.scalar h).derived (PX.scalar h).restriction
      (dl n).inverse (dl n).direct (PY.scalar h).derivedAdj (PX.scalar h).derivedAdj
      (dl n).adjunction (δ h) A B f
  · intro m n h A
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv (dl n).adjunction (dl m).adjunction
      (TwoSquare.mk _ _ _ _ (δ h).hom) A).symm
  · intro m n h H
    exact hit h H
  · intro m n h M
    apply (cancel_mono ((rd h).inv.app ((PX.evaluation n).obj M))).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    exact transition_mates ds.adjunction (dl m).adjunction (dl n).adjunction
      (PY.scalar h).restriction (PX.scalar h).restriction
      (PY.evaluation m) (PY.evaluation n) (PX.evaluation m) (PX.evaluation n)
      (ev m) (ev n) (δ h) (PY.transition h) (PX.transition h)
      (fun H ↦ hit h H) M

end Assembly

section CommonResolution

open CategoryTheory.MonoidalCategory
open scoped ZeroObject

universe a av b bv
variable {A : Type a} [Category.{av} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A] [HasColimitsOfSize.{0, 0} A]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ M : A, PreservesColimitsOfShape ℤ ((curriedTensor A).obj M)]
  [∀ M : A, PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj M)]
  [HasExactColimitsOfShape ℤ A]
  {B : Type b} [Category.{bv} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B] [HasColimitsOfSize.{0, 0} B]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ M : B, PreservesColimitsOfShape ℤ ((curriedTensor B).obj M)]
  [∀ M : B, PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj M)]
  [HasExactColimitsOfShape ℤ B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] (ad : F ⊣ G)
  (T : A ⥤ A) (π : T ⟶ 𝟭 A) [∀ M, Epi (π.app M)]
  (hT : ∀ M, ObjectProperty.flat (T.obj M) ∧ ObjectProperty.flat (F.obj (T.obj M)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include G ad π hT in
private theorem common_resolution (K : CochainComplex A ℤ) :
    ∃ (P : CochainComplex A ℤ) (q : P ⟶ K), QuasiIso q ∧
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P ∧
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) ∧
      (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, ObjectProperty.flat (F.obj (P.X i)) := by
  have := CochainComplex.closedUnderColimitsOfShape_flat A ℤ
  have := CochainComplex.closedUnderColimitsOfShape_flat B ℤ
  let good : ObjectProperty A :=
    fun M ↦ ObjectProperty.flat M ∧ ObjectProperty.flat (F.obj M)
  have : good.IsStableUnderRetracts :=
    ⟨fun e h ↦ ⟨ObjectProperty.prop_of_retract _ e h.1,
      ObjectProperty.prop_of_retract _ (e.map F) h.2⟩⟩
  have : good.ContainsZero :=
    ⟨0, isZero_zero A, ObjectProperty.prop_zero _,
      ObjectProperty.prop_of_isZero _ (F.map_isZero (isZero_zero A))⟩
  have (ι : Type) [Finite ι] : good.IsClosedUnderLimitsOfShape (Discrete ι) := by
    constructor
    rintro M ⟨p⟩
    exact ⟨ObjectProperty.prop_of_isLimit _ p.isLimit (fun j ↦ (p.prop_diag_obj j).1),
      ObjectProperty.prop_of_isLimit _ (isLimitOfPreserves F p.isLimit)
        (fun j ↦ (p.prop_diag_obj j).2)⟩
  have : HasFiniteProducts good.FullSubcategory :=
    ⟨fun n ↦ hasLimitsOfShape_of_closedUnderLimits (Discrete (Fin n)) good⟩
  have : HasFiniteBiproducts good.FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let Λ₀ : Abelian.LeftResolution good.ι :=
    { F := ObjectProperty.lift good T hT
      π := π }
  let Λ := Λ₀.reduced
  let P := Λ.resolutionFunctor.obj K
  let q := Λ.resolutionNatTrans.app K
  let presentation := Λ.colimitOfShapeResolutionFunctorObj K
  have hflat : good.ι.essImage ≤ ObjectProperty.flat := by
    rintro M ⟨N, ⟨i⟩⟩
    exact ObjectProperty.prop_of_iso _ i N.property.1
  refine ⟨P, q, inferInstance,
    (Λ.kFlat_resolutionFunctor_obj hflat K),
    ?_, ?_, ?_⟩
  · intro i
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i) presentation.isColimit)
      (fun j ↦ hflat _ ((presentation.prop_diag_obj j).1 i))
  · have : PreservesColimitsOfShape ℤ F := ad.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
    apply ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) presentation.isColimit)
    intro j
    obtain ⟨b, hb⟩ := (presentation.prop_diag_obj j).2
    have := hb
    have : CochainComplex.IsStrictlyLE
        ((F.mapHomologicalComplex (.up ℤ)).obj (presentation.diag.obj j)) b := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact F.map_isZero ((presentation.diag.obj j).isZero_of_isStrictlyLE b i hi)
    change (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj (presentation.diag.obj j))
    apply CochainComplex.kFlat_of_isStrictlyLE_of_flat _ b
    intro i
    obtain ⟨N, ⟨e⟩⟩ := (presentation.prop_diag_obj j).1 i
    exact ObjectProperty.prop_of_iso _ (F.mapIso e) N.property.2
  · intro i
    have : PreservesColimitsOfShape ℤ F := ad.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
    apply ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves
        (F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.eval B (.up ℤ) i)
        presentation.isColimit)
    intro j
    obtain ⟨N, ⟨e⟩⟩ := (presentation.prop_diag_obj j).1 i
    exact ObjectProperty.prop_of_iso _ (F.mapIso e) N.property.2

end CommonResolution

section FreeModules

open CategoryTheory.SheafFreeModule CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [EssentiallySmall.{w} C₀]
  {J₀ : GrothendieckTopology C₀}
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J₀ AddCommGrpCat.{w}]
  [HasWeakSheafify J₀ AddCommGrpCat.{w}]
  [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J₀ (Type w)]
  [J₀.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J₀.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (R : Sheaf J₀ CommRingCat.{w})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[no_expose, irreducible]
private def freeAdjunction : free R ⊣ underlyingRaw R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun E M ↦ Equiv.ofBijective _ (freeModule_restrict_bijective R E M)
    homEquiv_naturality_left_symm := by
      intro E E' M f g
      apply (freeModule_restrict_bijective R E M).1
      rw [(freeModule_restrict_naturality R E E' f M M).1]
      change (Equiv.ofBijective _ (freeModule_restrict_bijective R E M))
          ((Equiv.ofBijective _ (freeModule_restrict_bijective R E M)).symm (f ≫ g)) =
        f ≫ (Equiv.ofBijective _ (freeModule_restrict_bijective R E' M))
          ((Equiv.ofBijective _ (freeModule_restrict_bijective R E' M)).symm g)
      simp only [Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro E M N f g
      exact (freeModule_restrict_naturality R E E (𝟙 E) M N).2 f g }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem free_isFlat (E : Sheaf J₀ (Type w)) :
    IsFlatOnSite (J := J₀) (R := R) ((free R).obj E) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let a := PresheafOfModules.sheafification.{w} (𝟙 (ring R).obj)
  let U := SheafOfModules.forget.{w} (ring R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ring R).obj)
  let P := (PresheafOfModules.free (ring R).obj).obj E.obj
  have hP : PreservesFiniteLimits (tensorRight P) := by
    constructor
    intro K hK hfin
    constructor
    intro D
    constructor
    intro c hc
    have hflatX (X : C₀ᵒᵖ) : Module.Flat (R.obj.obj X) (P.obj X) := by
      change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
      infer_instance
    have hpres (X : C₀ᵒᵖ) : PreservesFiniteLimits
        (tensorRight (show ModuleCat (R.obj.obj X) from P.obj X)) := by
      have := hflatX X
      infer_instance
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
      isLimitOfPreserves (tensorRight
        (show ModuleCat (R.obj.obj X) from P.obj X))
          (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
  have : PreservesLimitsOfSize.{0, 0} U :=
    (PresheafOfModules.sheafificationAdjunction.{w}
      (𝟙 (ring R).obj)).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (tensorRight (a.obj P)) :=
    preservesFiniteLimits_of_natIso (tensorSheafificationIso_adapted R P).symm
  have : PreservesFiniteLimits (tensorLeft (a.obj P)) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (a.obj P)).symm
  have := tensorLeftColimits_adapted R (a.obj P)
  have := tensorRightColimits_adapted R (a.obj P)
  have h : ObjectProperty.flat (a.obj P) :=
    ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩
  exact flatOnSite_of_categorical_adapted R _ h

section AdaptedResolution

open scoped ZeroObject

variable {D₀ : Type u'} [Category.{v'} D₀] [EssentiallySmall.{w} D₀]
  {K₀ : GrothendieckTopology D₀}
  [K₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K₀.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K₀ AddCommGrpCat.{w}]
  [HasWeakSheafify K₀ AddCommGrpCat.{w}]
  [HasWeakSheafify K₀ CommRingCat.{w}] [HasWeakSheafify K₀ (Type w)]
  [K₀.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K₀.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (R' : Sheaf K₀ CommRingCat.{w})
  (L₀ : Sheaf J₀ (Type w) ⥤ Sheaf K₀ (Type w))
  (V₀ : Sheaf K₀ (Type w) ⥤ Sheaf J₀ (Type w)) (adj₀ : L₀ ⊣ V₀)
  (F₀ : SheafOfModules.{w} (ring R) ⥤ SheafOfModules.{w} (ring R'))
  (G₀ : SheafOfModules.{w} (ring R') ⥤ SheafOfModules.{w} (ring R))
  [F₀.Additive] [PreservesFiniteLimits F₀] (a₀ : F₀ ⊣ G₀)
  (e₀ : G₀ ⋙ underlyingRaw R ≅ underlyingRaw R' ⋙ V₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[no_expose, irreducible]
private def freeImageIso : free R ⋙ F₀ ≅ L₀ ⋙ free R' :=
  Adjunction.leftAdjointUniq
    (((freeAdjunction R).comp a₀).ofNatIsoRight e₀)
    (adj₀.comp (freeAdjunction R'))

-- The resolving subcategory carries two dependent monoidal structures.
include L₀ V₀ adj₀ G₀ a₀ e₀ in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_adapted_resolution
    (K : CochainComplex (SheafOfModules.{w} (ring R)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{w} (ring R)) ℤ) (q : P ⟶ K),
      QuasiIso q ∧ P.IsKFlatIndependentCoefficients ∧
        (∀ i : ℤ, IsFlatOnSite (J := J₀) (R := R) (P.X i)) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((F₀.mapHomologicalComplex (.up ℤ)).obj P) ∧
      (∀ i : ℤ, IsFlatOnSite (J := K₀) (R := R') (F₀.obj (P.X i))) := by
  let A := SheafOfModules.{w} (ring R)
  let B := SheafOfModules.{w} (ring R')
  have : HasColimitsOfSize.{w, w} A := inferInstance
  have : HasColimitsOfSize.{w, w} B := inferInstance
  have : HasLimitsOfSize.{w, w} A := inferInstance
  have : HasLimitsOfSize.{w, w} B := inferInstance
  have : HasFiniteProducts A := inferInstance
  have : HasFiniteProducts B := inferInstance
  have (I : Type w) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{w} (ring R).obj) := PresheafOfModules.hasColimitsOfShape _ _
  have (I : Type w) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{w} (ring R').obj) := PresheafOfModules.hasColimitsOfShape _ _
  have : HasFiniteCoproducts A := inferInstance
  have : HasFiniteCoproducts B := inferInstance
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive_adapted R
  have := hasTensor_adapted R
  have := hasGoodTensor₁₂_adapted R
  have := hasGoodTensor₂₃_adapted R
  have := hasTensor₄_adapted R
  have := all_tensorLeftColimits_adapted R
  have := all_tensorRightColimits_adapted R
  have (M : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).obj M) := inferInstance
  have (M : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ A := hasExactColimits_int_adapted R
  let := isMonoidal_W_independentCoefficients R'
  let := monoidalCategory R'
  let := symmetricCategory R'
  let := tensorPreadditive_adapted R'
  have := hasTensor_adapted R'
  have := hasGoodTensor₁₂_adapted R'
  have := hasGoodTensor₂₃_adapted R'
  have := hasTensor₄_adapted R'
  have := all_tensorLeftColimits_adapted R'
  have := all_tensorRightColimits_adapted R'
  have (M : B) : PreservesColimitsOfShape ℤ ((curriedTensor B).obj M) := inferInstance
  have (M : B) : PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ B := hasExactColimits_int_adapted R'
  let T := underlyingRaw R ⋙ free R
  have hT (M : A) : ObjectProperty.flat (T.obj M) ∧ ObjectProperty.flat (F₀.obj (T.obj M)) := by
    refine ⟨categorical_of_flatOnSite_adapted R _ (free_isFlat R _), ?_⟩
    exact ObjectProperty.prop_of_iso _
      ((freeImageIso R R' L₀ V₀ adj₀ F₀ G₀ a₀ e₀).app
        ((underlyingRaw R).obj M)).symm
      (categorical_of_flatOnSite_adapted R' _ (free_isFlat R' _))
  obtain ⟨P, q, hq, hp, hf, hfp, hff⟩ :=
    common_resolution F₀ G₀ a₀ T (freeAdjunction R).counit hT K
  exact ⟨P, q, hq, independent_of_categorical_adapted R _ hp,
    fun i ↦ flatOnSite_of_categorical_adapted R _ (hf i),
    independent_of_categorical_adapted R' _ hfp,
    fun i ↦ flatOnSite_of_categorical_adapted R' _ (hff i)⟩

end AdaptedResolution

end FreeModules

@[expose] public section

attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryRestrictionMate_isIso
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    {m n : ℕ} (h : n ≤ m) :
    IsIso (mateEquiv (S.levelAdj n) (S.levelAdj m)
      (TwoSquare.mk _ _ _ _ (S.restrictInverse h).hom)) := by
  have : HasWeakSheafify J AddCommGrpCat.{w} := inferInstance
  have : HasWeakSheafify K AddCommGrpCat.{w} := inferInstance
  exact restrictionMate_isIso (S.lift n).modules (S.right n) (S.levelAdj n)
    (S.lift m).modules (S.right m) (S.levelAdj m)
    (coefficientRestriction (J := J) O ell h) (coefficientRestriction (J := K) O ell h)
    (coefficientUnderlying (J := J) O ell m) (coefficientUnderlying (J := J) O ell n)
    (coefficientUnderlying (J := K) O ell m) (coefficientUnderlying (J := K) O ell n)
    L V adj (coefficientRestrictionUnderlying (J := J) O ell h)
    (coefficientRestrictionUnderlying (J := K) O ell h)
    (S.lift n).moduleUnderlying (S.lift m).moduleUnderlying
    (S.rightUnderlying n) (S.rightUnderlying m) (S.restrictInverse h)
    (S.levelTranspose n) (S.levelTranspose m) (S.restrictInverseUnderlying h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryEvaluationMate_eq
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj) (n : ℕ) :
    (mateEquiv S.systemAdj (S.levelAdj n)
      (TwoSquare.mk _ _ _ _ (S.inverseEvaluation n).inv)) =
        (S.rightEvaluation n).hom := by
  have : HasWeakSheafify J AddCommGrpCat.{w} := inferInstance
  have : HasWeakSheafify K AddCommGrpCat.{w} := inferInstance
  apply NatTrans.ext
  funext N
  let M := S.rightSystem.obj N
  let ε := S.systemAdj.counit.app N
  have h := S.systemTranspose M N ε n
  have he : S.systemAdj.homEquiv M N ε = 𝟙 M := by
    rw [Adjunction.homEquiv_unit, S.systemAdj.right_triangle_components]
  rw [he] at h
  erw [(coefficientEvaluation (J := J) (O := O) (ell := ell) n).map_id M,
    Category.id_comp] at h
  dsimp only [mateEquiv, TwoSquare.mk, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj]
  erw [Category.id_comp, Category.comp_id]
  change (S.levelAdj n).unit.app (M.level n) ≫
    (S.right n).map ((S.inverseEvaluation n).inv.app M) ≫
    (S.right n).map ((coefficientEvaluation (J := K) n).map ε) = _
  simpa only [Adjunction.homEquiv_unit, Functor.comp_map, Functor.map_comp, Category.assoc,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.id_obj, M, ε] using h.symm

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

private def transitionSets
    (P : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    {m n : ℕ} (h : n ≤ m) (M : CoefficientSystem (J := J) O ell) :=
  (coefficientUnderlying (J := J) O ell m).map ((P.strictTransition h).app M) ≫
    (coefficientRestrictionUnderlying (J := J) O ell h).hom.app (M.level n)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transitionSets_id
    (P : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (n : ℕ) (M : CoefficientSystem (J := J) O ell) :
    transitionSets O ell P (Nat.le_refl n) M = 𝟙 _ := by
  have h := congrArg ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map)
    (P.transitionsNormalized.1 n M)
  exact h.trans (CategoryTheory.Functor.map_id _ _)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transitionSets_comp
    (P : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m)
    (M : CoefficientSystem (J := J) O ell) :
    transitionSets O ell P (h₂.trans h₁) M =
      transitionSets O ell P h₁ M ≫ transitionSets O ell P h₂ M := by
  exact congrArg ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map)
    (P.transitionsNormalized.2.2 h₁ h₂ M) |>.trans (Functor.map_comp _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryInverseTransition
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell))
    {m n : ℕ} (h : n ≤ m) (M : CoefficientSystem (J := J) O ell) :
    (PX.strictTransition h).app (S.inverse.obj M) ≫
      (coefficientRestriction (J := K) O ell h).map ((S.inverseEvaluation n).hom.app M) =
    (S.inverseEvaluation m).hom.app M ≫
      (S.lift m).modules.map ((PY.strictTransition h).app M) ≫
      (S.restrictInverse h).hom.app (M.level n) := by
  have : HasWeakSheafify J AddCommGrpCat.{w} := inferInstance
  have : HasWeakSheafify K AddCommGrpCat.{w} := inferInstance
  let a (q : ℕ) :=
    (coefficientUnderlying (J := K) O ell q).map ((S.inverseEvaluation q).hom.app M) ≫
      (S.lift q).moduleUnderlying.hom.app (M.level q)
  have bridge {m n : ℕ} (h : n ≤ m) :
      (PX.strictTransition h).app (S.inverse.obj M) ≫
          (coefficientRestriction (J := K) O ell h).map
            ((S.inverseEvaluation n).hom.app M) =
        (S.inverseEvaluation m).hom.app M ≫
          (S.lift m).modules.map ((PY.strictTransition h).app M) ≫
          (S.restrictInverse h).hom.app (M.level n) ↔
      transitionSets O ell PX h (S.inverse.obj M) ≫ a n =
        a m ≫ L.map (transitionSets O ell PY h M) := by
    exact transition_bridge (F₀ := (S.lift n).modules) (F₁ := (S.lift m).modules)
      (RA := coefficientRestriction (J := J) O ell h)
      (RB := coefficientRestriction (J := K) O ell h)
      (Ua := coefficientUnderlying (J := J) O ell m)
      (Un := coefficientUnderlying (J := J) O ell n)
      (Ub := coefficientUnderlying (J := K) O ell m)
      (Uq := coefficientUnderlying (J := K) O ell n)
      (L := L) (ra := coefficientRestrictionUnderlying (J := J) O ell h)
      (rb := coefficientRestrictionUnderlying (J := K) O ell h)
      (mu₀ := (S.lift n).moduleUnderlying) (mu₁ := (S.lift m).moduleUnderlying)
      (β := S.restrictInverse h) (S.restrictInverseUnderlying h)
      (M.level n) (M.level m) ((S.inverse.obj M).level n) ((S.inverse.obj M).level m)
      ((S.inverseEvaluation n).hom.app M) ((S.inverseEvaluation m).hom.app M)
      ((PX.strictTransition h).app (S.inverse.obj M)) ((PY.strictTransition h).app M)
  apply bridge h |>.2
  induction m, h using Nat.le_induction with
  | base =>
    rw [transitionSets_id, transitionSets_id]
    dsimp only [coefficientEvaluation, Functor.comp_obj] at a ⊢
    simp only [L.map_id, Category.id_comp, Category.comp_id]
  | succ m h ih =>
    have hs := S.inverseTransition m M
    rw [← PY.transitionsNormalized.2.1 m M,
      ← PX.transitionsNormalized.2.1 m (S.inverse.obj M)] at hs
    have hs' := (bridge (Nat.le_succ m)).1 hs
    change transitionSets O ell PX (h.trans (Nat.le_succ m)) _ ≫ a n =
      a (m + 1) ≫ L.map (transitionSets O ell PY (h.trans (Nat.le_succ m)) M)
    have hX := transitionSets_comp O ell PX (Nat.le_succ m) h (S.inverse.obj M)
    have hY := transitionSets_comp O ell PY (Nat.le_succ m) h M
    rw [hX, hY, L.map_comp, Category.assoc, ih, ← Category.assoc, hs', Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Elaborate the dependent normalized comparison equations.
/-- Derived direct image commutes with evaluation, including its canonical mates.
Source: Zheng, Construction 4.1 and Lemma 4.10, printed pp. 21 and 23--24.

Proof: Present systems as modules over the quotient-ring sheaf on the sequence site.
That site is essentially small in the coefficient universe, so its module category
has K-injective resolutions. Exact inverse image descends termwise; K-injective
resolutions give total right derived image. Localize the ordinary adjunction with
the canonical fraction-transpose formula to obtain the specified derived adjunction.
On a flat-term K-flat complex P at level n, inverse image commutes with the extension
E_n: both are zero above n, and below n they agree by the inverse-image/tensor
comparison. On quotient tensor generators this is x tensor a mapped to u* x tensor a.
It commutes with reduction of a. The comparison therefore respects the extension
maps sigma and descends to u* LE_n = LE_n u*. The chain of the two LE_n/e_n adjunctions
and the system and level geometric adjunctions gives, naturally in both arguments,
Hom(A,e_n Ru* M) = Hom(A,Ru* e_n M). Yoneda gives directEvaluation. The component at
n of the extension comparison is the identity, so transposing the evaluated counit
proves the counit equation; the triangle identities give the unit equation.
Exact scalar restriction descends termwise. Its left adjoint is derived scalar
extension, computed by the same flat-term K-flat complexes; the pullback/tensor
comparison gives derivedTensor with its representative formula. Composition of the
right derived direct images with restriction gives restrictedDirect. Transposing the
tensor comparison gives exactly restrictedDirect_mate. The localized ordinary
restriction/inverse-image isomorphism gives restrictedInverse; transposing its
underlying identity gives restrictedInverse_mate. On complexes the inverse evaluation
square is the ordinary transition square. For direct image, transpose the sigma
compatibility through the Hom chain above. Its explicit sigma-mate formula is exactly
directTransition. These arguments are natural in every derived system morphism and
use no preservation of K-injectives by evaluation or flatness of a coefficient quotient.
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
theorem coefficientSystemUnboundedComparison
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) :
    Nonempty (CoefficientSystemUnboundedImage O ell L V adj S PY PX) := by
  have : HasWeakSheafify J AddCommGrpCat.{w} := inferInstance
  have : HasWeakSheafify K AddCommGrpCat.{w} := inferInstance
  let := strictRingSystem_isGrothendieckAbelian
    (coefficientRings (J := K) (O := O) (ell := ell))
  let : IsGrothendieckAbelian.{w} (CoefficientSystem (J := K) O ell) :=
    IsGrothendieckAbelian.of_equivalence
      (coefficientSystemEquivalence (J := K) (O := O) (ell := ell)).symm
  let (n : ℕ) : IsGrothendieckAbelian.{w}
      (coefficientLevelModules (J := K) O ell n) :=
    isGrothendieckAbelian_coefficientUniverse _
  let : PreservesFiniteLimits S.inverse := S.systemExact.1
  let : PreservesFiniteColimits S.inverse := S.systemExact.2
  let (n : ℕ) : PreservesFiniteLimits (S.lift n).modules := (S.inverseExact n).1
  let (n : ℕ) : PreservesFiniteColimits (S.lift n).modules := (S.inverseExact n).2
  obtain ⟨ds⟩ := derivedImage_exists S.inverse S.rightSystem S.systemAdj
  have hl (n : ℕ) : Nonempty
      (CoefficientDerivedImage (S.lift n).modules (S.right n) (S.levelAdj n)) :=
    derivedImage_exists (S.lift n).modules (S.right n) (S.levelAdj n)
  have dl : ∀ n, CoefficientDerivedImage (S.lift n).modules (S.right n) (S.levelAdj n) :=
    fun n ↦ Classical.choice (hl n)
  obtain ⟨E, ⟨T⟩⟩ := comparison_assembly S.inverse S.rightSystem S.systemAdj
    (fun n ↦ (S.lift n).modules) S.right S.levelAdj PY PX
    S.inverseEvaluation (fun {_ _} h ↦ S.restrictInverse h) ds dl
    (fun n ↦ exists_adapted_resolution
      (coefficientQuotientSheaf (J := J) O ell n)
      (coefficientQuotientSheaf (J := K) O ell n) L V adj
      (S.lift n).modules (S.right n) (S.levelAdj n) (S.rightUnderlying n))
    (fun {_ _} h ↦ ordinaryRestrictionMate_isIso O ell L V adj S h)
    (fun n ↦ show IsIso (mateEquiv S.systemAdj (S.levelAdj n)
      (TwoSquare.mk _ _ _ _ (S.inverseEvaluation n).inv)) by
        rw [ordinaryEvaluationMate_eq O ell L V adj S n]
        infer_instance)
    (fun {_ _} h ↦ ordinaryInverseTransition O ell L V adj S PY PX h)
  exact ⟨⟨E, T⟩⟩

end

end SheafOfModules
