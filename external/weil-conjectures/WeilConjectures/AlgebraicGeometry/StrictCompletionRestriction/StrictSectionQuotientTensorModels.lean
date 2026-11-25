/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.Algebra.Homology.FlatSingleTensor.RingedFlatSingleTensorCohomology
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionQuotientConeMaps
import all WeilConjectures.Algebra.Homology.KFlatRoos.KFlatRoosRepresentativeInvariance
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Localization.Predicate
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Normalized tensor models for section principal quotients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj TensorProduct
open CategoryTheory.InternalAbelianSheafModule

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction

private theorem uncurry_map_identity {A B D : Type*}
    [Category A] [Category B] [Category D] (F : A ⥤ B ⥤ D)
    {P P' : A} (f : P ⟶ P') (Q : B) :
    (Functor.uncurry.obj F).map (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q) =
      (F.map f).app Q := by
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id]

private def uncurry_flip_iso {A B D : Type*}
    [Category A] [Category B] [Category D] (F : A ⥤ B ⥤ D) (Q : B) :
    Prod.sectL A Q ⋙ Functor.uncurry.obj F ≅ F.flip.obj Q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P P' f
    change (Functor.uncurry.obj F).map (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q) ≫
        𝟙 _ = 𝟙 _ ≫ (F.map f).app Q
    simpa only [Category.comp_id, Category.id_comp] using uncurry_map_identity F f Q)

private theorem uncurry_flip_iso_hom_app {A B D : Type*}
    [Category A] [Category B] [Category D] (F : A ⥤ B ⥤ D) (Q : B) (P : A) :
    (uncurry_flip_iso F Q).hom.app P = 𝟙 _ := rfl

private theorem normalized_iso_square {D : Type*} [Category D]
    {U V W A B S : D} (e : U ≅ A) (m : B ≅ V) (s : V ≅ W)
    (d : S ≅ W) (b : S ≅ B) (f : U ⟶ V) (g : A ⟶ B)
    (hb : b.hom = d.hom ≫ (m ≪≫ s).inv)
    (hn : g ≫ m.hom = e.inv ≫ f) :
    f ≫ s.hom ≫ d.inv ≫ b.hom = e.hom ≫ g := by
  simp only [hb, Iso.inv_hom_id_assoc, Iso.trans_inv,
    Iso.hom_inv_id_assoc]
  apply (Iso.comp_inv_eq m).2
  simpa only [Category.assoc] using (Iso.inv_comp_eq e).1 hn.symm

private theorem iso_factor_inverse {D : Type*} [Category D]
    {A B C E : D} (e : A ≅ B) (b : C ≅ E) (ε : E ≅ B) (δ : C ⟶ A)
    (h : δ ≫ e.hom = b.hom ≫ ε.hom) :
    ε.inv ≫ b.inv ≫ δ = e.inv := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private theorem mapped_composite_square {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) {U U' : B} {V V' W W' : A}
    (a : U ⟶ U') (r : U ⟶ Q.obj V) (r' : U' ⟶ Q.obj V')
    (g : V ⟶ V') (s : V ⟶ W) (s' : V' ⟶ W') (h : W ⟶ W')
    (hr : a ≫ r' = r ≫ Q.map g) (hs : g ≫ s' = s ≫ h) :
    a ≫ (r' ≫ Q.map s') = (r ≫ Q.map s) ≫ Q.map h := by
  rw [← Category.assoc, hr, Category.assoc, ← Q.map_comp, hs, Q.map_comp]
  simp only [Category.assoc]

private theorem mapped_factor {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) {K V W : A} {U : B}
    (f : Q.obj K ⟶ U) (r : U ⟶ Q.obj V)
    (a : K ⟶ V) (b : V ⟶ W) (c : K ⟶ W)
    (hr : f ≫ r = Q.map a) (hc : a ≫ b = c) :
    f ≫ (r ≫ Q.map b) = Q.map c := by
  rw [← Category.assoc, hr, ← Q.map_comp, hc]

private theorem quotient_iso_square {D : Type*} [Category D]
    {A A' B B' C C' : D} (a : A ≅ C) (a' : A' ≅ C')
    (b : B ≅ C) (b' : B' ≅ C') (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (ha : f ≫ a'.hom = a.hom ≫ h) (hb : g ≫ b'.hom = b.hom ≫ h) :
    f ≫ (a' ≪≫ b'.symm).hom = (a ≪≫ b.symm).hom ≫ g := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ha, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun k ↦ a.hom ≫ k)
  apply (Iso.comp_inv_eq b').2
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun k ↦ b.inv ≫ k) hb.symm

private theorem resolution_comparison {A D : Type*} [Category A] [Category D]
    (S T : A ⥤ D) (F : A ⥤ A) (π : F ⟶ 𝟭 A) (b : F ⋙ T ≅ F ⋙ S)
    (hS : ∀ X, IsIso (S.map (π.app X))) :
    ∃ m : S ⟶ T,
      (∀ X, IsIso (T.map (π.app X)) → IsIso (m.app X)) ∧
      (∀ (X : A) (e : T.obj X ≅ S.obj X),
        T.map (π.app X) ≫ e.hom = b.hom.app X ≫ S.map (π.app X) →
          m.app X = e.inv) := by
  let ε : F ⋙ S ⟶ S := Functor.whiskerRight π S
  have hε (X) : IsIso (ε.app X) := hS X
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  let m : S ⟶ T := inv ε ≫ b.inv ≫ Functor.whiskerRight π T
  refine ⟨m, ?_, ?_⟩
  · intro X ht
    let := ht
    change IsIso ((inv ε).app X ≫ b.inv.app X ≫ T.map (π.app X))
    infer_instance
  · intro X e hn
    change ((asIso ε).app X).inv ≫ (b.app X).inv ≫ T.map (π.app X) = _
    exact iso_factor_inverse e (b.app X) ((asIso ε).app X) _ hn

attribute [local irreducible] derivedInternalHomOfUniverses CoefficientClosedStructure.tensor
  SheafOfModules.monoidalCategory
attribute [local irreducible] coefficientTotalTensor CoefficientTensorModels.iso
section TensorLocalization
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

private abbrev SC := SheafOfModules.{u + 1} ((sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
private abbrev CC := CochainComplex (SC J R) ℤ
variable [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} ((sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
private abbrev DC := DerivedCategory.{u + 1} (SC J R)
private abbrev KF (P : CC J R) :=
  CochainComplex.IsKFlatIndependentCoefficients (R := R) P
private abbrev total := coefficientTotalTensor.{u, u + 1, u} J R

variable (H : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} J R))
  (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} J R H)

private abbrev tensorSource :=
  ((DerivedCategory.Q : CC J R ⥤ DC J R).prod DerivedCategory.Q) ⋙ H.tensor
private abbrev tensorTarget := total J R ⋙ DerivedCategory.Q

private theorem model_naturality
    (P P' Q Q' : CC J R) (hP : KF J R P) (hP' : KF J R P')
    (hQ : KF J R Q) (hQ' : KF J R Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((total J R).map (f, g)) ≫
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM P' Q' hP' hQ').hom =
      (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM P Q hP hQ).hom ≫
        H.tensor.map
          (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
          (Y := (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q'))
          (DerivedCategory.Q.map f, DerivedCategory.Q.map g) := by
  simpa only [CoefficientTensorModels.iso, coefficientKFlatInclusion,
    Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj, ObjectProperty.ι_map, ObjectProperty.homMk,
    CategoryTheory.Iso.app_hom, total, Prod.mkHom, id_eq] using
    HM.comparison.hom.naturality
    (X := (⟨P, hP⟩, ⟨Q, hQ⟩)) (Y := (⟨P', hP'⟩, ⟨Q', hQ'⟩))
    (ObjectProperty.homMk f, ObjectProperty.homMk g)

attribute [local semireducible] coefficientTotalTensor
private theorem tensor_comparison :
    ∃ m : tensorSource J R H ⟶ tensorTarget J R,
      (∀ (P Y : CC J R), KF J R P → IsIso (m.app (P, Y))) ∧
      (∀ (P Q : CC J R) (hP : KF J R P) (hQ : KF J R Q),
        m.app (P, Q) =
          (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM P Q hP hQ).inv) := by
  obtain ⟨F, π, hπ, hk, _⟩ := SheafOfModules.functorial_resolution R
  let F₂ := F.prod F
  let π₂ : F₂ ⟶ 𝟭 _ :=
    { app Y := (π.app Y.1, π.app Y.2)
      naturality Y Z f := by
        apply Prod.hom_ext
        · exact π.naturality f.1
        · exact π.naturality f.2 }
  obtain ⟨b, hb⟩ :
      ∃ b : F₂ ⋙ tensorTarget J R ≅ F₂ ⋙ tensorSource J R H,
        ∀ Y, b.hom.app Y =
          (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM
            (F.obj Y.1) (F.obj Y.2) (hk Y.1) (hk Y.2)).hom := by
    refine ⟨NatIso.ofComponents
      (fun Y ↦ CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM
        _ _ (hk Y.1) (hk Y.2))
      (fun {Y Z} f ↦ model_naturality J R H HM _ _ _ _
        (hk Y.1) (hk Z.1) (hk Y.2) (hk Z.2) (F.map f.1) (F.map f.2)), ?_⟩
    intro Y
    rfl
  have hS (Y) : IsIso ((tensorSource J R H).map (π₂.app Y)) := by
    have := hπ Y.1
    have := hπ Y.2
    change IsIso (H.tensor.map
      (X := (DerivedCategory.Q.obj (F.obj Y.1), DerivedCategory.Q.obj (F.obj Y.2)))
      (Y := (DerivedCategory.Q.obj Y.1, DerivedCategory.Q.obj Y.2))
      (DerivedCategory.Q.map (π.app Y.1), DerivedCategory.Q.map (π.app Y.2)))
    have hi : IsIso (Prod.mkHom (DerivedCategory.Q.map (π.app Y.1))
        (DerivedCategory.Q.map (π.app Y.2))) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    exact Functor.map_isIso H.tensor _
  obtain ⟨m, hm, hnorm⟩ := resolution_comparison (tensorSource J R H)
    (tensorTarget J R) F₂ π₂ b hS
  refine ⟨m, ?_, ?_⟩
  · intro P Y hP
    apply hm (P, Y)
    have h₁ : QuasiIso
        (((SheafOfModules.KFlatFixedTensor.totalTensor R).map (π.app P)).app
          (F.obj Y)) :=
      CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R
        (F.obj Y) (hk Y) (π.app P) (hπ P)
    have h₂ : QuasiIso
        (((SheafOfModules.KFlatFixedTensor.totalTensor R).obj P).map (π.app Y)) :=
      SheafOfModules.left_tensor_quasiIso R P hP (π.app Y) (hπ Y)
    have hfac : (tensorTarget J R).map (π₂.app (P, Y)) =
        DerivedCategory.Q.map
          ((((SheafOfModules.KFlatFixedTensor.totalTensor R).map (π.app P)).app (F.obj Y)) ≫
            ((SheafOfModules.KFlatFixedTensor.totalTensor R).obj P).map (π.app Y)) :=
      SheafOfModules.tensorTarget_map R (π.app P) (π.app Y)
    rw [hfac, DerivedCategory.Q.map_comp]
    exact IsIso.comp_isIso'
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h₁)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h₂)
  · intro P Q hP hQ
    have hn := model_naturality J R H HM _ P _ Q (hk P) hP (hk Q) hQ
      (π.app P) (π.app Q)
    change (tensorTarget J R).map (π₂.app (P, Q)) ≫
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM P Q hP hQ).hom =
      (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM
        (F.obj P) (F.obj Q) (hk P) (hk Q)).hom ≫
        (tensorSource J R H).map (π₂.app (P, Q)) at hn
    apply hnorm (P, Q)
      (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} _ R H HM P Q hP hQ)
    rw [hb]
    exact hn

private theorem extend_kflat_iso (F G : DC J R ⥤ DC J R)
    (c : ∀ (P : CC J R), KF J R P → (F.obj (DerivedCategory.Q.obj P) ≅
      G.obj (DerivedCategory.Q.obj P)))
    (hc : ∀ (P P' : CC J R) (hP : KF J R P) (hP' : KF J R P') (f : P ⟶ P'),
      F.map (DerivedCategory.Q.map f) ≫ (c P' hP').hom =
        (c P hP).hom ≫ G.map (DerivedCategory.Q.map f)) :
    ∃ b : F ≅ G, ∀ (P : CC J R) (hP : KF J R P),
      b.hom.app (DerivedCategory.Q.obj P) = (c P hP).hom := by
  obtain ⟨K, π, hπ, hk, _⟩ := SheafOfModules.functorial_resolution R
  let ε : K ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q :=
    Functor.whiskerRight π DerivedCategory.Q
  have hε (P) : IsIso (ε.app P) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hπ P)
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  let a : (K ⋙ DerivedCategory.Q) ⋙ F ≅ (K ⋙ DerivedCategory.Q) ⋙ G :=
    NatIso.ofComponents (fun P ↦ c (K.obj P) (hk P))
      (fun {P P'} f ↦ hc _ _ (hk P) (hk P') (K.map f))
  let d : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    Functor.isoWhiskerRight (asIso ε).symm F ≪≫ a ≪≫
      Functor.isoWhiskerRight (asIso ε) G
  let b : F ≅ G := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SC J R) (.up ℤ))
    (DerivedCategory.Q ⋙ F) (DerivedCategory.Q ⋙ G) F G d
  refine ⟨b, ?_⟩
  intro P hP
  have hn := hc (K.obj P) P (hk P) hP (π.app P)
  change F.map (DerivedCategory.Q.map (π.app P)) ≫ (c P hP).hom =
    (c (K.obj P) (hk P)).hom ≫ G.map (DerivedCategory.Q.map (π.app P)) at hn
  change (Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (SC J R) (.up ℤ))
    (DerivedCategory.Q ⋙ F) (DerivedCategory.Q ⋙ G) F G d.hom).app
      (DerivedCategory.Q.obj P) = _
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]
  dsimp only [d, a, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, asIso_inv, asIso_hom,
    NatIso.ofComponents_hom_app]
  change (F.mapIso ((asIso ε).app P)).inv ≫
    (c (K.obj P) (hk P)).hom ≫ (G.mapIso ((asIso ε).app P)).hom = _
  exact (Iso.inv_comp_eq (F.mapIso ((asIso ε).app P))).2 hn.symm

end TensorLocalization

section Singleton
attribute [local semireducible] coefficientTotalTensor
attribute [local irreducible] CochainComplex.mapBifunctorSingle₂Iso
  SheafOfModules.siteSheafTensorRightIso
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})
private abbrev GS := SheafOfModules.{u + 1}
  ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
private abbrev GC := CochainComplex (GS J R) ℤ
private abbrev GT := coefficientTotalTensor.{u, u + 1, u} J R
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
open MonoidalCategory

@[irreducible] private def singleComparisonNatural (N : GS J R) :
    Prod.sectL (GC J R) ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ⋙ GT J R ≅
      (SheafOfModules.siteSheafTensorRight N).mapHomologicalComplex (.up ℤ) :=
  uncurry_flip_iso
    ((curriedTensor (GS J R)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
      ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ≪≫
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor (GS J R)) N ≪≫
    NatIso.mapHomologicalComplex (SheafOfModules.siteSheafTensorRightIso R N).symm (.up ℤ)

@[irreducible] private def singleComparison (N : GS J R) (P : GC J R) :
    (GT J R).obj (P, (HomologicalComplex.single _ (.up ℤ) 0).obj N) ≅
      ((SheafOfModules.siteSheafTensorRight N).mapHomologicalComplex (.up ℤ)).obj P :=
  (singleComparisonNatural J R N).app P

private theorem presentation_hom (M N : GS J R) :
    (SheafOfModules.tensorRightPresentation R N).hom.app M =
      (SheafOfModules.tensorObjIsoSheafification M N).hom := by
  have hi : ((SheafOfModules.tensorRightPresentation R N).app M).inv =
      (SheafOfModules.tensorObjIsoSheafification M N).inv := by
    dsimp only [SheafOfModules.tensorRightPresentation, Iso.app_inv, Iso.trans_inv,
      NatTrans.comp_app,
      Functor.mapIso_inv, Iso.symm_inv, NatIso.ofComponents_inv_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom,
      NatIso.ofComponents_hom_app]
    simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
      MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorHom_def]
    rfl
  exact congrArg Iso.hom (Iso.ext_inv hi)

private theorem tensorComparison_pure (M N : GS J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    ((SheafOfModules.siteSheafTensorRightIso R N).inv.app M).val.app U
      (CochainPullback.moduleTmul (R := R) M N U x y) =
        SheafOfModules.siteSheafTensorTmul M N U x y := by
  let a := PresheafOfModules.sheafification (𝟙
    ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  have he : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫
      (SheafOfModules.siteSheafTensorRightIso R N).inv.app M =
        a.map ((SheafOfModules.siteTensorRightIso R N.val).inv.app M.val) := by
    simp only [SheafOfModules.siteSheafTensorRightIso, NatTrans.comp_app,
      Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [presentation_hom, Iso.inv_hom_id_assoc]
    rfl
  change ((adj.unit.app (M.val ⊗ N.val) ≫
    ((SheafOfModules.tensorObjIsoSheafification M N).inv ≫
      (SheafOfModules.siteSheafTensorRightIso R N).inv.app M).val).app U)
        (x ⊗ₜ[R.obj.obj U] y) = _
  erw [he]
  exact (congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] y))
    (adj.unit.naturality ((SheafOfModules.siteTensorRightIso R N.val).inv.app M.val))).symm

attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification
private theorem singleComparison_values (N : GS J R) (P : GC J R)
    (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : N.val.obj U) :
    ((singleComparison J R N P).hom.f p).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} J R P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N) p 0 p (add_zero p) U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y)) =
      SheafOfModules.siteSheafTensorTmul (P.X p) N U x y := by
  have hc := SheafOfModules.FlatSingleTensor.collapse_ι
    (curriedTensor (GS J R)) N P p
  unfold singleComparison singleComparisonNatural GT coefficientTotalTensor
  simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    uncurry_flip_iso_hom_app]
  dsimp only [HomologicalComplex.comp_f]
  change ((SheafOfModules.siteSheafTensorRightIso R N).inv.app (P.X p)).val.app U
    (((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (GS J R)) N P).hom.f p).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} J R P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N) p 0 p (add_zero p) U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y))) = _
  -- The total comparison is identity on its sole surviving summand.
  have hval :
      ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (GS J R)) N P).hom.f p).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} J R P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj N) p 0 p (add_zero p) U x
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y)) =
        CochainPullback.moduleTmul (R := R) (P.X p) N U x y := by
    have hgen : coefficientTensorGenerator.{u, u + 1, u} J R P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N) p 0 p (add_zero p) U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y) =
        (HomologicalComplex.ιMapBifunctor P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj N) (curriedTensor (GS J R))
          (.up ℤ) p 0 p (add_zero p)).val.app U
          (CochainPullback.moduleTmul (R := R) (P.X p)
            (((HomologicalComplex.single _ (.up ℤ) 0).obj N).X 0) U x
              ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y)) := by
      exact CategoryTheory.RingedDerivedNative.generator_eq.{u + 1, u, u} J R P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N) p 0 p (add_zero p) U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y)
    have hcollapse :
        ((curriedTensor (GS J R)).obj (P.X p)).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫
          HomologicalComplex.ιMapBifunctor P
            ((HomologicalComplex.single _ (.up ℤ) 0).obj N) (curriedTensor (GS J R))
            (.up ℤ) p 0 p (add_zero p) ≫
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (GS J R)) N P).hom.f p =
            𝟙 _ := by
      erw [hc]
      exact (((curriedTensor (GS J R)).obj (P.X p)).mapIso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N)).inv_hom_id
    have hpure := CochainPullback.moduleTmul_map (R := R) (𝟙 (P.X p))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv U x y
    have hpure' :
        (((curriedTensor (GS J R)).obj (P.X p)).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv).val.app U
          (CochainPullback.moduleTmul (R := R) (P.X p) N U x y) =
        CochainPullback.moduleTmul (R := R) (P.X p)
          (((HomologicalComplex.single _ (.up ℤ) 0).obj N).X 0) U x
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app U y) := by
      simpa only [curriedTensor_obj_map, curriedTensor_obj_obj, ← id_tensorHom,
        SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using hpure
    rw [hgen, ← hpure']
    have hv := congrArg (fun f ↦ f.val.app U
      (CochainPullback.moduleTmul (R := R) (P.X p) N U x y)) hcollapse
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app] at hv
    exact hv.trans (by rfl)
  erw [hval]
  exact tensorComparison_pure J R (P.X p) N U x y

private theorem singleComparison_naturality (N : GS J R)
    {P P' : GC J R} (f : P ⟶ P') :
    (GT J R).map (f, 𝟙 ((HomologicalComplex.single _ (.up ℤ) 0).obj N)) ≫
        (singleComparison J R N P').hom =
      (singleComparison J R N P).hom ≫
        ((SheafOfModules.siteSheafTensorRight N).mapHomologicalComplex (.up ℤ)).map f := by
  unfold singleComparison
  exact (singleComparisonNatural J R N).hom.naturality f

end Singleton

section Assembly
attribute [local irreducible] SheafOfModules.KFlatRoos.algebraModule
attribute [local implicit_reducible] HomologicalComplex.asFunctor Prod.sectL
attribute [local irreducible] CochainComplex.mapBifunctorSingle₂Iso
  SheafOfModules.siteSheafTensorRightIso PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification
attribute [local irreducible] SheafOfModules.KFlatRoos.tensorUnit
  SheafOfModules.siteSheafTensorRight SheafOfModules.KFlatRoos.roos
  SheafOfModules.siteSheafTensorTmul coefficientTensorGenerator
variable (X : Scheme.{u})
  (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (H : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X) R))
  (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X) R H)
  (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (ι : (Functor.const ℕᵒᵖ).obj R ⟶ B)

-- Check the simultaneous normalization and all three representative equations together.
private theorem reductionModels
    (T : Presentation.{u + 2, u + 1, u + 1} (SC (Scheme.ProEt.topology X) R))
    (hc : ∀ (P : CC (Scheme.ProEt.topology X) R) (_hP : KF (Scheme.ProEt.topology X) R P),
      ∃ c : ∀ n : ℕ, (T.tower.obj P).asFunctor.obj (op n) ⟶
          (SheafOfModules.KFlatRoos.level.{u + 1, u, u + 1} B ι n).obj P,
        (∀ n : ℕ, QuasiIso (c n)) ∧
        (∀ (n : ℕ) (q : ℤ), (c n).f q =
          (T.coordinates P n q).hom ≫
            (biprod.fst : P.X q ⊞ P.X (q + 1) ⟶ P.X q) ≫
            (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1}
              (ι.app (op n))).app (P.X q))) :
    Nonempty (SectionReductionModelsFor X R T H HM B ι) := by
  classical
  obtain ⟨c, hquasi, hcoord⟩ :
      ∃ c : ∀ (P : CC (Scheme.ProEt.topology X) R), KF (Scheme.ProEt.topology X) R P → ∀ n : ℕ,
          (T.tower.obj P).asFunctor.obj (op n) ⟶
            (SheafOfModules.KFlatRoos.level B ι n).obj P,
        (∀ (P : CC (Scheme.ProEt.topology X) R) (hP : KF (Scheme.ProEt.topology X) R P) (n :
          ℕ), QuasiIso (c P hP n)) ∧
        (∀ (P : CC (Scheme.ProEt.topology X) R) (hP : KF (Scheme.ProEt.topology X) R P) (n : ℕ)
          (q : ℤ),
          (c P hP n).f q = (T.coordinates P n q).hom ≫
            (biprod.fst : P.X q ⊞ P.X (q + 1) ⟶ P.X q) ≫
            (SheafOfModules.KFlatRoos.tensorUnit (ι.app (op n))).app (P.X q)) := by
    choose c hq hc' using hc
    exact ⟨c, hq, hc'⟩
  let L := SheafOfModules.KFlatRoos.level.{u + 1, u, u + 1} B ι
  let N := SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι
  let single (n : ℕ) (P : CC (Scheme.ProEt.topology X) R) :
      (total (Scheme.ProEt.topology X) R).obj (P, (HomologicalComplex.single (SC
        (Scheme.ProEt.topology X) R) (.up ℤ) 0).obj (N n)) ≅
        (L n).obj P := singleComparison (Scheme.ProEt.topology X) R (N n) P
  have hc_nat (n : ℕ) (P P' : CC (Scheme.ProEt.topology X) R) (hP : KF (Scheme.ProEt.topology
    X) R P) (hP' : KF (Scheme.ProEt.topology X) R P')
      (f : P ⟶ P') :
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (T.tower.map f)).app (op n)) ≫ c P' hP' n =
        c P hP n ≫ (L n).map f := by
    ext q : 1
    have hd := T.diagonal f n q
    have hu := (SheafOfModules.KFlatRoos.tensorUnit (ι.app (op n))).naturality (f.f q)
    simp only [HomologicalComplex.comp_f, hcoord]
    change ((T.tower.map f).f q).app (op n) ≫
      (T.coordinates P' n q).hom ≫ _ = _
    erw [reassoc_of% hd, Category.assoc, biprod.map_fst_assoc]
    erw [hu, Category.assoc]
    rfl
  obtain ⟨model, hmodel⟩ :
      ∃ model : ∀ (n : ℕ) (P : CC (Scheme.ProEt.topology X) R)
        (hP : KF (Scheme.ProEt.topology X) R P),
          (T.reduction n).obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((L n).obj P),
        ∀ (n : ℕ) (P : CC (Scheme.ProEt.topology X) R)
          (hP : KF (Scheme.ProEt.topology X) R P),
          (model n P hP).hom = (T.reduction_descent n).hom.app P ≫
            DerivedCategory.Q.map (c P hP n) := by
    refine ⟨fun n P hP ↦ (T.reduction_descent n).app P ≪≫
      (@asIso _ _ _ _ (DerivedCategory.Q.map (c P hP n))
        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hquasi P hP n))), ?_⟩
    intro n P hP
    rfl
  have model_nat (n : ℕ) (P P' : CC (Scheme.ProEt.topology X) R) (hP : KF
    (Scheme.ProEt.topology X) R P) (hP' : KF (Scheme.ProEt.topology X) R P')
      (f : P ⟶ P') :
      (T.reduction n).map (DerivedCategory.Q.map f) ≫ (model n P' hP').hom =
        (model n P hP).hom ≫ DerivedCategory.Q.map ((L n).map f) := by
    have hd := (T.reduction_descent n).hom.naturality f
    dsimp only [Functor.comp_map] at hd
    simp only [hmodel]
    exact mapped_composite_square DerivedCategory.Q _ _ _ _ _ _ _ hd
      (hc_nat n P P' hP hP' f)
  obtain ⟨m, hm, hnorm⟩ := tensor_comparison (Scheme.ProEt.topology X) R H HM
  let target (n : ℕ) : DC (Scheme.ProEt.topology X) R ⥤ DC (Scheme.ProEt.topology X) R :=
    Prod.sectL _ (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (N n))) ⋙
      H.tensor
  let tensorSingle (n : ℕ) (P : CC (Scheme.ProEt.topology X) R) (hP : KF (Scheme.ProEt.topology
    X) R P) :
      (target n).obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj ((L n).obj P) :=
    (@asIso _ _ _ _
      (m.app (P, (HomologicalComplex.single (SC (Scheme.ProEt.topology X) R)
        (.up ℤ) 0).obj (N n)))
      (hm P ((HomologicalComplex.single (SC (Scheme.ProEt.topology X) R)
        (.up ℤ) 0).obj (N n)) hP)) ≪≫ DerivedCategory.Q.mapIso (single n P)
  have tensorSingle_nat (n : ℕ) (P P' : CC (Scheme.ProEt.topology X) R)
      (hP : KF (Scheme.ProEt.topology X) R P) (hP' : KF (Scheme.ProEt.topology X) R P') (f : P
        ⟶ P') :
      (target n).map (DerivedCategory.Q.map f) ≫ (tensorSingle n P' hP').hom =
        (tensorSingle n P hP).hom ≫ DerivedCategory.Q.map ((L n).map f) := by
    have hn := m.naturality (X := (P, (HomologicalComplex.single _ (.up ℤ) 0).obj (N n)))
      (Y := (P', (HomologicalComplex.single _ (.up ℤ) 0).obj (N n))) (f, 𝟙 _)
    change H.tensor.map
      (X := (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (N n))))
      (Y := (DerivedCategory.Q.obj P',
        DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (N n))))
      (DerivedCategory.Q.map f,
        DerivedCategory.Q.map (𝟙 ((HomologicalComplex.single (SC (Scheme.ProEt.topology X) R)
          (.up ℤ) 0).obj (N n)))) ≫
        _ = _ at hn
    erw [DerivedCategory.Q.map_id] at hn
    change (target n).map (DerivedCategory.Q.map f) ≫
      m.app (P', (HomologicalComplex.single (SC (Scheme.ProEt.topology X) R) (.up ℤ) 0).obj (N n)) =
      m.app (P, (HomologicalComplex.single (SC (Scheme.ProEt.topology X) R) (.up ℤ) 0).obj (N n)) ≫
        DerivedCategory.Q.map ((total (Scheme.ProEt.topology X) R).map
          (X := (P, (HomologicalComplex.single (SC (Scheme.ProEt.topology X) R) (.up ℤ) 0).obj
            (N n)))
          (Y := (P', (HomologicalComplex.single (SC (Scheme.ProEt.topology X) R) (.up ℤ) 0).obj
            (N n)))
          (f, 𝟙 _)) at hn
    simpa only [tensorSingle, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      single, L, SheafOfModules.KFlatRoos.level, N] using
      mapped_composite_square DerivedCategory.Q _ _ _ _ _ _ _ hn
        (singleComparison_naturality (Scheme.ProEt.topology X) R (N n) f)
  have normalized (n : ℕ) :
      ∃ b : T.reduction n ≅ target n, ∀ (P : CC (Scheme.ProEt.topology X) R) (hP : KF
        (Scheme.ProEt.topology X) R P),
        b.hom.app (DerivedCategory.Q.obj P) =
          (model n P hP).hom ≫ (tensorSingle n P hP).inv := by
    apply extend_kflat_iso (Scheme.ProEt.topology X) R (T.reduction n) (target n)
      (fun P hP ↦ model n P hP ≪≫ (tensorSingle n P hP).symm)
    intro P P' hP hP' f
    exact quotient_iso_square _ _ _ _ _ _ _
      (model_nat n P P' hP hP' f) (tensorSingle_nat n P P' hP hP' f)
  obtain ⟨tensor, htensor⟩ :
      ∃ tensor : ∀ n : ℕ, T.reduction n ≅ target n,
        ∀ (n : ℕ) (P : CC (Scheme.ProEt.topology X) R) (hP : KF (Scheme.ProEt.topology X) R P),
          (tensor n).hom.app (DerivedCategory.Q.obj P) =
            (model n P hP).hom ≫ (tensorSingle n P hP).inv := by
    choose tensor htensor using normalized
    exact ⟨tensor, htensor⟩
  refine ⟨{
    single := single
    single_values := fun n P p U x y ↦
      singleComparison_values (Scheme.ProEt.topology X) R (N n) P p U x y
    tensor := tensor
    model := model
    unit := ?_
    step := ?_
    tensor_model := ?_ }⟩
  · intro n P hP
    have hu : T.augmentation.app P ≫ roosEval (T.tower.obj P) n ≫ c P hP n =
        (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (SheafOfModules.KFlatRoos.tensorUnit (ι.app (op n))) (.up ℤ)).app P := by
      ext i : 1
      obtain ⟨j, hj⟩ := (Equiv.addRight (1 : ℤ)).surjective i
      change j + 1 = i at hj
      subst i
      simp only [HomologicalComplex.comp_f, hcoord, roosEval_f, Category.assoc]
      erw [reassoc_of% (T.augmentation_level P n j)]
      erw [biprod.inl_fst_assoc, Category.id_comp]
      rfl
    simp only [hmodel]
    exact mapped_factor DerivedCategory.Q _ _ _ _ _ (T.reduction_unit_descent n P)
      ((Category.assoc _ _ _).trans hu)
  · intro n P hP
    have hs : (T.tower.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ c P hP n =
        c P hP (n + 1) ≫ SheafOfModules.KFlatRoos.transition B ι P n := by
      ext i : 1
      have ht := congrArg (fun f ↦ f ≫ biprod.fst ≫
        (SheafOfModules.KFlatRoos.tensorUnit (ι.app (op n))).app (P.X i))
          (T.transition P n i)
      simp only [Category.assoc] at ht
      erw [biprod.map_fst_assoc, Category.id_comp] at ht
      have h := congrArg (fun η ↦ η.app (P.X i))
        (SheafOfModules.KFlatRoos.tensorUnit_levelMap B ι n)
      simp only [NatTrans.comp_app] at h
      simp only [HomologicalComplex.comp_f, hcoord,
        SheafOfModules.KFlatRoos.transition, NatTrans.mapHomologicalComplex_app_f]
      change _ = (T.coordinates P (n + 1) i).hom ≫ biprod.fst ≫
        (SheafOfModules.KFlatRoos.tensorUnit (ι.app (op (n + 1)))).app (P.X i) ≫
        (SheafOfModules.siteSheafTensorRightMap
          (SheafOfModules.KFlatRoos.levelMap B ι n)).app (P.X i)
      erw [h]
      exact ht
    simp only [hmodel]
    exact mapped_composite_square DerivedCategory.Q _ _ _ _ _ _ _
      (T.reduction_step_descent n P) hs
  · intro n P Q hP hQ q _hq
    apply heq_of_eq
    have hn := m.naturality (X := (P, Q))
      (Y := (P, (HomologicalComplex.single _ (.up ℤ) 0).obj (N n))) (𝟙 P, q)
    change H.tensor.map (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
      (Y := (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (N n))))
      (DerivedCategory.Q.map (𝟙 P), DerivedCategory.Q.map q) ≫
      m.app (P, (HomologicalComplex.single _ (.up ℤ) 0).obj (N n)) =
      m.app (P, Q) ≫ DerivedCategory.Q.map ((total (Scheme.ProEt.topology X) R).map (𝟙 P, q)) at hn
    erw [DerivedCategory.Q.map_id, hnorm P Q hP hQ] at hn
    simpa only [Functor.map_comp, Category.assoc, Functor.mapIso_hom, Iso.app_hom,
      tensorSource, Functor.comp_obj, Functor.prod_obj, Prod.sectL,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors, total, N] using
      normalized_iso_square
      (CoefficientTensorModels.iso (Scheme.ProEt.topology X) R H HM P Q hP hQ)
      (@asIso _ _ _ _
        (m.app (P, (HomologicalComplex.single _ (.up ℤ) 0).obj (N n)))
        (hm P ((HomologicalComplex.single _ (.up ℤ) 0).obj (N n)) hP))
      (DerivedCategory.Q.mapIso (single n P)) (model n P hP)
      ((tensor n).app (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.map ((total (Scheme.ProEt.topology X) R).map
        (X := (P, Q))
        (Y := (P, (HomologicalComplex.single _ (.up ℤ) 0).obj (N n))) (𝟙 P, q)))
      (H.tensor.map (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
        (Y := (DerivedCategory.Q.obj P,
          DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (N n))))
        (𝟙 _, DerivedCategory.Q.map q)) (htensor n P hP) hn

end Assembly

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized tensor identification of the section reductions, without the
completion assertion.

Source: blueprint latest, integral-ctf-equals-bc proof, Locality; first-reduction
Cones paragraph; Stacks 03EK, 06YS, 06YT and 08TC
(blueprint: lem-sfb-strict-section-quotient-tensor-models).

Proof: use strictSectionQuotientConeMaps for the normalized quasi-isomorphism
from each scalar cone to termwise tensor with the quotient. Its component formula
implies naturality in the complex and identifies the inclusion and successor
squares, giving model, unit and step after localization. Collapse total tensor
with a degree-zero singleton by its sole (p,0) summand and compare the monoidal
tensor with the site tensor. Sheafification naturality proves the prescribed
local pure-tensor formula, giving single and single_values.

Extend the supplied HM comparison by functorial K-flat resolution in both
variables. It is invertible whenever the first factor is K-flat and agrees with
HM on two K-flat factors. Combine it with single to identify model with derived
tensor on K-flat representatives. Functorial resolution extends this natural
isomorphism to all complexes, and localization descends it to the derived
category without altering those representative values. Naturality in every
quotient resolution Q gives tensor_model.
No flatness of the quotient or boundedness of P is used.
For the empty site all these maps are the unique maps; a zero quotient gives
zero tensor objects, and the same formulas still apply. -/
theorem strictSectionQuotientTensorModels (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (Modules (DerivedNakayama.integerRing l E) X))
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hscalar : ∀ (M : Modules (DerivedNakayama.integerRing l E) X) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
      (T.scalar.asHom.app M).val.app U x = sectionScalarValue l E X data.d U • x)
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (ι : (Functor.const ℕᵒᵖ).obj (ring (DerivedNakayama.integerRing l E) X) ⟶ B)
    (hB : ∀ n : ℕ, B.obj (op n) = sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.finiteRing l E X n))
    (hι : ∀ n : ℕ, HEq (ι.app (op n))
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.quotient l E X n)))
    (hstep : ∀ n : ℕ, HEq (B.map (homOfLE (Nat.le_succ n)).op)
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.transition l E X n)))
    (H : CoefficientClosedStructure (hom (DerivedNakayama.integerRing l E) X))
    (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (ring (DerivedNakayama.integerRing l E) X) H)
    (t : TensorComparison (DerivedNakayama.integerRing l E) X H HM) :
      Nonempty (SectionReductionModels l E X T H HM B ι) := by
  have _ := hstep
  have _ := t
  clear hstep t
  apply reductionModels X (ring (DerivedNakayama.integerRing l E) X) H HM B ι T
  intro P hP
  simpa only [] using
    strictSectionQuotientConeMaps l E X T data hdata hscalar B ι hB hι P hP

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
