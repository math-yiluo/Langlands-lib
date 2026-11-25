/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionRoofModels
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
import WeilConjectures.AlgebraicGeometry.Injective.InjectiveSectionUnitComparison
import WeilConjectures.AlgebraicGeometry.Square.SquareSectionUnitCancellation
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf

/-! # The normalized derived square on an injective roof

Source: Stacks Project, Cohomology, Tags 01FB, 0D5T and 0D5X.
(blueprint: lem-weil-pbc-square-injective-roof-action).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coefficient_augmentation {X Z : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ)
    (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L)
    (beta : I.cocomplex ⟶ L)
    (hbeta : I.ι.f 0 ≫ beta.f 0 = φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0) :
    I.ι' ≫ HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor X.Modules 0).map φ ≫
        (HomologicalComplex.singleMapHomologicalComplex (pushforward v)
          (ComplexShape.up ℤ) 0).inv.app G ≫
        ((pushforward v).mapHomologicalComplex (ComplexShape.up ℤ)).map J.ι' ≫
        (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
        HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat := by
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory] at *
  let : (pushforward v).Additive := inferInstanceAs (pushforward v).Additive
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, InjectiveResolution.ι'_f_zero,
    Functor.mapHomologicalComplex_map_f]
  rw [HomologicalComplex.extendMap_f beta _ (i := 0) (by simp),
    HomologicalComplex.extendMap_f ell _ (i := 0) (by simp)]
  simp only [InjectiveResolution.cochainComplexXIso, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
  rw [HomologicalComplex.mapExtendX_hom_eq _ _ (show ComplexShape.embeddingUpNat.r 0 = some 0 by
    simpa using ComplexShape.embeddingUpNat.r_f 0)]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_hom, HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    eqToIso.inv, reassoc_of% hbeta, CochainComplex.single₀_obj_zero, Category.id_comp,
    CochainComplex.singleFunctor, Functor.comp_obj,
    HomologicalComplex.single_map_f_self, Iso.refl_inv,
    HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_inv_app,
    ↓reduceDIte, eqToHom_refl, Functor.map_comp, eqToHom_map, eqToIso.hom,
    eqToHom_trans_assoc, Category.assoc]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalSingle_unitQ {X Z : Scheme.{u}} (v : Z ⟶ X) (G : Z.Modules) :
    canonicalSingleDirectImageMap v G =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (pushforward v) (.up ℤ) 0).inv.app G) ≫
        (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
          ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G) := by
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory] at *
  simp only [canonicalSingleDirectImageMap, Functor.rightDerivedFunctorUnitQ,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem roof_algebra {C : Type*} [Category C] {A B D E K N : C}
    (i : A ⟶ B) (j : K ⟶ N) (e : D ⟶ E) [IsIso j] [IsIso e]
    (b : B ⟶ E) (a : A ⟶ D) (u : D ⟶ N) (c : A ⟶ K)
    (h₁ : i ≫ b = a ≫ e) (h₂ : c ≫ j = a ≫ u) :
    c = i ≫ b ≫ inv e ≫ u ≫ inv j := by
  apply (cancel_mono j).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [h₂]
  have ha : (i ≫ b) ≫ inv e = a := by
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
      congrArg (fun t ↦ t ≫ inv e) h₁
  simp only [← Category.assoc, ha]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_derived_roof {X Z : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ)
    (ell : ((pushforward v).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶ L)
    (hell : QuasiIso ell) (beta : I.cocomplex ⟶ L)
    (hbeta : I.ι.f 0 ≫ beta.f 0 = φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0) :
    let ellZ := (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
      HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat
    let t := (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
      J.cochainComplex ≫ (schemeDerivedDirectImage v).map (inv (DerivedCategory.Q.map J.ι'))
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map φ ≫
      canonicalSingleDirectImageMap v G =
    DerivedCategory.Q.map I.ι' ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat) ≫
      inv (DerivedCategory.Q.map ellZ) ≫ t := by
  intro ellZ t
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory] at *
  let : QuasiIso ell := hell
  have he : QuasiIso ellZ := by dsimp only [ellZ]; infer_instance
  let := he
  let a := (CochainComplex.singleFunctor X.Modules 0).map φ ≫
    (HomologicalComplex.singleMapHomologicalComplex (pushforward v) (.up ℤ) 0).inv.app G ≫
      ((pushforward v).mapHomologicalComplex (.up ℤ)).map J.ι'
  have h₁ : DerivedCategory.Q.map I.ι' ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat) =
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map ellZ := by
    simpa only [Functor.map_comp, a, ellZ, Category.assoc] using
      congrArg DerivedCategory.Q.map (coefficient_augmentation v F G φ I J L ell beta hbeta)
  have h₂ : ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map φ ≫
      canonicalSingleDirectImageMap v G) ≫
        (schemeDerivedDirectImage v).map (DerivedCategory.Q.map J.ι') =
      DerivedCategory.Q.map a ≫
        (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
          J.cochainComplex := by
    rw [canonicalSingle_unitQ]
    simp only [Category.assoc]
    rw [← Functor.rightDerivedFunctorUnitQ_naturality]
    simp only [a, Functor.map_comp, Category.assoc]
    rfl
  have hh := roof_algebra (DerivedCategory.Q.map I.ι')
    ((schemeDerivedDirectImage v).map (DerivedCategory.Q.map J.ι'))
    (DerivedCategory.Q.map ellZ)
    (DerivedCategory.Q.map (HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat))
    (DerivedCategory.Q.map a)
    ((RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
      J.cochainComplex) _ h₁ h₂
  simpa only [t, Functor.map_inv, Category.assoc] using hh

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem roof_action_algebra {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {A B E J N : C} {RI RJ RL : D}
    (i : A ⟶ B) (beta : B ⟶ E) (ell : J ⟶ E) (t : J ⟶ N) [IsIso ell]
    (c : A ⟶ N) (b : RI ⟶ P.obj A) (d : P.obj N ⟶ RJ)
    (uI : RI ⟶ P.obj B) (uJ : RJ ⟶ P.obj J) (uL : RL ⟶ P.obj E)
    (hb : RI ⟶ RL) (he : RJ ⟶ RL) [IsIso he]
    (hc : c = i ≫ beta ≫ inv ell ≫ t) (hs : b ≫ P.map i = uI)
    (hn : hb ≫ uL = uI ≫ P.map beta) (hd : he ≫ uL = uJ ≫ P.map ell)
    (hu : uJ ≫ P.map t ≫ d = 𝟙 RJ) : b ≫ P.map c ≫ d ≫ he = hb := by
  have hr : uL ≫ P.map (inv ell) ≫ P.map t ≫ d = inv he := by
    apply (cancel_epi he).mp
    rw [← Category.assoc, hd]
    simpa only [Category.assoc, Functor.map_inv, IsIso.hom_inv_id_assoc,
      IsIso.hom_inv_id] using hu
  simp only [hc, P.map_comp, Category.assoc]
  rw [reassoc_of% hs, ← reassoc_of% hn, reassoc_of% hr]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem roof_sections_quasiIso {X Z : Scheme.{u}} (v : Z ⟶ X)
    {G : Z.Modules} (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ) (hL : ∀ n : ℕ, Injective (L.X n))
    (ell : ((pushforward v).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶ L)
    (hell : QuasiIso ell) (U : X.Opens) :
    QuasiIso (((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
      (.up ℤ)).map ((J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
        (pushforward v)).hom ≫ HomologicalComplex.extendMap ell
          ComplexShape.embeddingUpNat)) := by
  let : QuasiIso ell := hell
  let : ∀ n : ℕ, Injective (L.X n) := hL
  let : J.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective J.cochainComplex 0
  let : CochainComplex.IsKInjective (L.extend ComplexShape.embeddingUpNat) :=
    CochainComplex.isKInjective_of_injective (L.extend ComplexShape.embeddingUpNat) 0
  let ellZ := (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
    HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat
  have hZ : QuasiIso ellZ := by dsimp only [ellZ]; infer_instance
  let := hZ
  have hP := RingedSpace.localSections_directImage_resolution_quasiIso
    v.toLRSHom.toShHom J.cochainComplex (L.extend ComplexShape.embeddingUpNat) ellZ
  let E := (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let := hP
  have hE : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map
      (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
        (.up ℤ)).map ellZ)) := by infer_instance
  exact hE

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived square, on raw section cohomology, is represented by its augmented
injective roof. This statement contains no classical cohomology or restricted resolution.
Source: Stacks Project, Tag 01FB (Remark explain-arrow), Tag 0D5T (composition of
right-derived direct images), Tag 0D5X (local derived sections)
(blueprint: lem-weil-pbc-square-injective-roof-action).

Proof: Extend I, J and L by zero to integer indices. Their injective terms and lower bound
make them K-injective. The augmentation equation identifies the derived coefficient map
with Q(beta) followed by the inverse of Q(ell), using naturality of the right-derived unit
and of the single-complex comparison. The direct-image square mate theorem and the pasted
unit equation identify the two routes through Rf Rv and Rg Rk with the sectionwise ordinary
pushforward comparison. Compute local sections on these representatives. Naturality of the
local derived-sections unit and its universal factorization for local Leray carry the two
arrows to Gamma(U,beta) and Gamma(U,ell). Exact evaluation commutes with homology. The
inverse-open comparison uses the same K-injective representative as its local model;
its two model comparisons therefore cancel. The raw endpoint comparisons are exactly
squareInjectiveLocalComparison, so postcomposing with H(Gamma(U,ell)) gives the displayed
numerator equation. The argument is valid on empty opens and in degree zero and requires
neither flatness nor preservation of injectives by v_* or f_*. -/
theorem square_injectiveRoof_action {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ) (hL : ∀ n : ℕ, Injective (L.X n))
    (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L)
    (hell : QuasiIso ell) (beta : I.cocomplex ⟶ L)
    (hbeta : I.ι.f 0 ≫ beta.f 0 = φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0)
    (q : ℕ) (V : S.Opens) :
    let U := f ⁻¹ᵁ V
    let Γ := (RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℤ) (q : ℤ)
    let ellZ := (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
      HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat
    let betaZ := HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat
    (squareInjectiveLocalComparison f F q V I U rfl).hom ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        (derivedSquareUnitMap f k g v h F G φ)).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).inv ≫
      H.map (Γ.map ellZ) = H.map (Γ.map betaZ) := by
  intro U Γ H ellZ betaZ
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory] at *
  let : QuasiIso ell := hell
  have hZ : QuasiIso ellZ := by dsimp only [ellZ]; infer_instance
  let := hZ
  have hΓ := roof_sections_quasiIso v J L hL ell hell U
  let := hΓ
  have hE : IsIso (H.map (Γ.map ellZ)) := by
    change IsIso (HomologicalComplex.homologyMap (Γ.map ellZ) (q : ℤ))
    infer_instance
  let := hE
  let P := schemeDerivedDirectImage f ⋙
    RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ) ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let c := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map φ ≫
      canonicalSingleDirectImageMap v G
  let t := (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
    J.cochainComplex ≫ (schemeDerivedDirectImage v).map (inv (DerivedCategory.Q.map J.ι'))
  let d := ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
      ((derivedSquareRightComparison f k g v h).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app (op V) ≫
    (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
      ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
    (squareInverseOpenComparison g (q : ℤ)
      ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
    (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).inv
  have hu : directImageSectionUnitAt f (q : ℤ) V
      (((pushforward v).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ≫
        P.map t ≫ d = 𝟙 _ := by
    simpa only [RingedSpace.localHypercohomologyPresheaf, Functor.map_comp,
      NatTrans.comp_app, Category.assoc, P, t, d, U, Functor.comp_map,
      CategoryTheory.evaluation_obj_map] using
      squareSectionUnit_cancellation f k g v h G J q V
  have hc : c = DerivedCategory.Q.map I.ι' ≫ DerivedCategory.Q.map betaZ ≫
      inv (DerivedCategory.Q.map ellZ) ≫ t :=
    coefficient_derived_roof v F G φ I J L ell hell beta hbeta
  have hs := injectiveSectionUnit_comparison f F q V I
  have hn := directImageSectionUnitAt_naturality f (q : ℤ) V betaZ
  have hd := directImageSectionUnitAt_naturality f (q : ℤ) V ellZ
  have hh := roof_action_algebra P (DerivedCategory.Q.map I.ι')
    (DerivedCategory.Q.map betaZ) (DerivedCategory.Q.map ellZ) t c
    (squareInjectiveLocalComparison f F q V I U rfl).hom d
    (directImageSectionUnitAt f (q : ℤ) V I.cochainComplex)
    (directImageSectionUnitAt f (q : ℤ) V
      (((pushforward v).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex))
    (directImageSectionUnitAt f (q : ℤ) V (L.extend ComplexShape.embeddingUpNat))
    (H.map (Γ.map betaZ)) (H.map (Γ.map ellZ)) hc hs hn hd hu
  simpa only [derivedSquareUnitMap, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, P, c, d, U, Γ, H, Functor.comp_map,
    CategoryTheory.evaluation_obj_map] using hh

end AlgebraicGeometry
