/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Vanishing at one section under restriction of scalars -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory

private theorem commute_four
    {A : Type*} [Category A] {X₀ X₁ X₂ X₃ X₄ : A}
    {f₀ : X₀ ⟶ X₀} {f₁ : X₁ ⟶ X₁} {f₂ : X₂ ⟶ X₂}
    {f₃ : X₃ ⟶ X₃} {f₄ : X₄ ⟶ X₄}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄}
    (h₁ : f₀ ≫ a = a ≫ f₁) (h₂ : f₁ ≫ b = b ≫ f₂)
    (h₃ : f₂ ≫ c = c ≫ f₃) (h₄ : f₃ ≫ d = d ≫ f₄) :
    f₀ ≫ (a ≫ b ≫ c ≫ d) = (a ≫ b ≫ c ≫ d) ≫ f₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

private theorem derived_products
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{u} A] [HasCountableProducts A] :
    HasCountableProducts (DerivedCategory A) := by
  classical
  constructor
  intro T _
  constructor
  intro F
  let K : T → CochainComplex A ℤ := fun t ↦
    (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj
      (DerivedCategory.Q.objPreimage (F.obj ⟨t⟩))
  have hK (t : T) : (K t).IsKInjective := inferInstance
  have h := (CochainComplex.termwise_product_isKInjective_and_isLimit K).2
  have : HasLimit (Discrete.functor K ⋙ DerivedCategory.Q) := ⟨⟨_, h.some⟩⟩
  have e (t : Discrete T) : DerivedCategory.Q.obj (K t.as) ≅ F.obj t := by
    let η := (CochainComplex.toKInjectiveResolution.{u} A).app
      (DerivedCategory.Q.objPreimage (F.obj t))
    have : QuasiIso η :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
    exact (asIso (DerivedCategory.Q.map η)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (F.obj t)
  exact hasLimit_of_iso (show Discrete.functor K ⋙ DerivedCategory.Q ≅ F from
    Discrete.natIso e)

private theorem conjugate_isIso_iff
    {A : Type*} [Category A] {X Y : A} (e : X ≅ Y)
    (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ e.hom = e.hom ≫ g) :
    IsIso f ↔ IsIso g := by
  have h₁ : g = e.inv ≫ f ≫ e.hom := by rw [h]; simp
  have h₂ : f = e.hom ≫ g ≫ e.inv := by rw [← Category.assoc, ← h]; simp
  constructor
  · intro hf
    have := hf
    rw [h₁]
    infer_instance
  · intro hg
    have := hg
    rw [h₂]
    infer_instance

private theorem towerIso_map_iff
    {A B : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] [F.ReflectsIsomorphisms]
    (K : ℕ → A) [HasProduct K] [HasProduct (fun n ↦ F.obj (K n))]
    [PreservesLimit (Discrete.functor K) F] (f : ∀ n, K (n + 1) ⟶ K n) :
    IsIso (towerTransitionEndomorphism f) ↔
      IsIso (towerTransitionEndomorphism (K := fun n ↦ F.obj (K n)) (fun n ↦ F.map (f n))) := by
  let e := PreservesProduct.iso F K
  have he : F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (K := fun n ↦ F.obj (K n)) (fun n ↦ F.map (f n)) := by
    apply Pi.hom_ext
    intro n
    dsimp only [e]
    simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
    rw [← F.map_comp,
      (towerTransitionEndomorphism_eq_iff f _).mp rfl n, F.map_sub, F.map_comp]
    simp [towerTransitionEndomorphism, towerProductShift]
  exact (isIso_iff_of_reflects_iso _ F).symm.trans (conjugate_isIso_iff e _ _ he)

private theorem towerIso_of_iso
    {A : Type*} [Category A] [Preadditive A] [HasCountableProducts A]
    {X Y : A} (e : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : f ≫ e.hom = e.hom ≫ g) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ X) (fun _ ↦ f)) ↔
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ Y) (fun _ ↦ g)) := by
  let ep := Pi.mapIso (fun _ : ℕ ↦ e)
  have he : towerTransitionEndomorphism (K := fun _ : ℕ ↦ X) (fun _ ↦ f) ≫ ep.hom =
      ep.hom ≫ towerTransitionEndomorphism (K := fun _ : ℕ ↦ Y) (fun _ ↦ g) :=
    (towerTransitionEndomorphism_natural_backward _ _ (fun _ ↦ e.hom)
      (fun _ ↦ h.symm)).symm
  exact conjugate_isIso_iff ep _ _ he

private theorem derived_reflectsIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((DerivedCategory.homologyFunctor B n).map (F.mapDerivedCategory.map f)) :=
      inferInstance
    have : IsIso (F.map ((DerivedCategory.homologyFunctor A n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2 (by
        dsimp only [Functor.comp_map]
        infer_instance)
    exact isIso_of_reflects_iso _ F

private noncomputable def scalar_slice_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (U : C)
    (M : ringedSiteModules.{u} (localCoefficientRings B)) :
    let F := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let G := SheafOfModules.restrictScalars.{u}
      ((J.overPullback RingCat U).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))
    G.obj ((SheafOfModules.overFunctor.{u} (localCoefficientRings B) U).obj M) ≅
      (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).obj (F.obj M) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ Iso.refl _) ?_
  intro V W g
  ext x
  rfl

private noncomputable def scalar_slice_complex_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (U : C)
    (P : CochainComplex (ringedSiteModules.{u} (localCoefficientRings B)) ℤ) :
    letI := (localCoefficientRestriction_exact R U).1
    letI := (localCoefficientRestriction_exact B U).1
    let F := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let G := SheafOfModules.restrictScalars.{u}
      ((J.overPullback RingCat U).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))
    (G.mapHomologicalComplex (.up ℤ)).obj
      (((SheafOfModules.overFunctor.{u} (localCoefficientRings B) U).mapHomologicalComplex
        (.up ℤ)).obj P) ≅
    ((SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).mapHomologicalComplex
      (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  have := (localCoefficientRestriction_exact R U).1
  have := (localCoefficientRestriction_exact B U).1
  dsimp only
  refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ scalar_slice_iso R B φ U (P.X n)) ?_
  intro i j hij
  ext V x
  rfl

private theorem scalar_complex_mul_commute
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (U : C)
    (f : R.obj.obj (op U))
    (P : CochainComplex (ringedSiteModules.{u} (localCoefficientRings B)) ℤ) :
    letI := (localCoefficientRestriction_exact R U).1
    letI := (localCoefficientRestriction_exact B U).1
    let F := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let G := SheafOfModules.restrictScalars.{u}
      ((J.overPullback RingCat U).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))
    (G.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex
        (localSectionMultiplicationNatTrans B U (φ.hom.app (op U) f)) (.up ℤ)).app P) ≫
        (scalar_slice_complex_iso R B φ U P).hom =
    (scalar_slice_complex_iso R B φ U P).hom ≫
      (NatTrans.mapHomologicalComplex
        (localSectionMultiplicationNatTrans R U f) (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  have := (localCoefficientRestriction_exact R U).1
  have := (localCoefficientRestriction_exact B U).1
  dsimp only
  ext n V x
  change B.obj.map V.unop.hom.op (φ.hom.app (op U) f) •
      (show (P.X n).val.obj (op V.unop.left) from x) =
    φ.hom.app (op V.unop.left) (R.obj.map V.unop.hom.op f) •
      (show (P.X n).val.obj (op V.unop.left) from x)
  have hn : B.obj.map V.unop.hom.op (φ.hom.app (op U) f) =
      φ.hom.app (op V.unop.left) (R.obj.map V.unop.hom.op f) :=
    (congrArg (fun k ↦ k f) (φ.hom.naturality V.unop.hom.op)).symm
  exact congrArg (fun b : B.obj.obj (op V.unop.left) ↦
    b • (show (P.X n).val.obj (op V.unop.left) from x)) hn

private theorem multiplication_fac
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (P : CochainComplex (ringedSiteModules.{u} (localCoefficientRings R)) ℤ) :
    letI := (localCoefficientRestriction_exact R U).1
    letI := (localCoefficientRestriction_exact R U).2.1
    letI := (localCoefficientRestriction_exact R U).2.2
    let T := SheafOfModules.overFunctor.{u} (localCoefficientRings R) U
    (localSectionDerivedMultiplication R U f).app (DerivedCategory.Q.obj P) ≫
        T.mapDerivedCategoryFactors.hom.app P =
      T.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (localSectionMultiplicationNatTrans R U f)
          (.up ℤ)).app P) := by
  have := (localCoefficientRestriction_exact R U).1
  have := (localCoefficientRestriction_exact R U).2.1
  have := (localCoefficientRestriction_exact R U).2.2
  dsimp only
  simp only [localSectionDerivedMultiplication, Localization.liftNatTrans_app,
    Category.assoc]
  let T := SheafOfModules.overFunctor.{u} (localCoefficientRings R) U
  change _ ≫ (_ ≫
    (T.mapDerivedCategoryFactors.inv.app P ≫ T.mapDerivedCategoryFactors.hom.app P)) = _
  rw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem completeElement_iff_towerIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)))
    (U : C) (f : R.obj.obj (op U))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)] :
    IsRingedSiteCompleteElement J R K U f ↔
      IsIso (towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
        (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) := by
  have := (localCoefficientRestriction_exact R U).1
  have := (localCoefficientRestriction_exact R U).2.1
  have := (localCoefficientRestriction_exact R U).2.2
  have he : ringedSiteSectionLocalization (localCoefficientRings R) U f =
      localCoefficientLocalization R U f := by
    unfold ringedSiteSectionLocalization localCoefficientLocalization
    congr 2
    funext n
    ext V
    change (1 : R.obj.obj (op V.unop.left)) * R.obj.map V.unop.hom.op f =
      R.obj.map V.unop.hom.op f * 1
    exact mul_comm _ _
  let eK :=
    ((localCoefficientDerivedRestriction R U).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage K)
  obtain ⟨T, hT⟩ := (exists_isDerivedLimit_and_iso
    (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
    (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)).1
  have hcriterion := localHom_zero_iff_multiplicationTower_zero J R U f K T hT
  obtain ⟨p, δ, hδ⟩ := hT
  have hzero := Triangle.isZero₁_iff_isIso₂
    (Triangle.mk p (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
      (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) δ) hδ
  change IsZero T ↔ IsIso (towerTransitionEndomorphism
    (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
    (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) at hzero
  rw [← hzero, ← hcriterion]
  let eL := (DerivedCategory.singleFunctor _ 0).mapIso (eqToIso he)
  let eH := (derivedInternalHom (J.over U) (R.over U)).mapIso
    (eL.symm.op.prod eK.symm)
  exact ⟨fun h ↦ h.of_iso eH.symm, fun h ↦ h.of_iso eH⟩

/-- Local completeness at one section is unchanged by restricting scalars.
Source: Stacks Project, algebraization.tex, Tag 099C, proof, last two sentences.
Proof: Tag 0997 and the Roos distinguished triangle identify completeness with
invertibility of one minus the product shift. Derived products exist by termwise
products of K-injective resolutions. Restriction is exact and conservative and its
derived functor is a right adjoint, hence preserves products and reflects
isomorphisms (by cohomology). The product comparison identifies the two product
shifts. Exact slice restriction commutes with scalar restriction through the
componentwise identity isomorphism; its multiplication square commutes by
naturality of the ring map. Conjugating the product shifts proves the equivalence.
This works for every section without an ideal, finite generation or boundedness.
(auxiliary; not a blueprint node). -/
theorem restrictScalars_completeElement_iff
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).over U))]
    (M : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
    (U : C) (f : R.obj.obj (op U)) :
    IsRingedSiteCompleteElement J R
      (DerivedCategory.Q.obj
        (((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage M))) U f ↔
      IsRingedSiteCompleteElement J B M U (φ.hom.app (op U) f) := by
  classical
  let R₀ := localCoefficientRings R
  let B₀ := localCoefficientRings B
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let φU : R.over U ⟶ B.over U := (J.overPullback CommRingCat U).map φ
  let G := SheafOfModules.restrictScalars.{u}
    ((J.overPullback RingCat U).map
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))
  let TR := SheafOfModules.overFunctor.{u} R₀ U
  let TB := SheafOfModules.overFunctor.{u} B₀ U
  have := (localCoefficientRestriction_exact R U).1
  have := (localCoefficientRestriction_exact R U).2.1
  have := (localCoefficientRestriction_exact R U).2.2
  have := (localCoefficientRestriction_exact B U).1
  have := (localCoefficientRestriction_exact B U).2.1
  have := (localCoefficientRestriction_exact B U).2.2
  have := SheafOfModules.isGrothendieckAbelian (R₀.over U)
  have := SheafOfModules.isGrothendieckAbelian (B₀.over U)
  have hRP : HasCountableProducts
      (DerivedCategory (ringedSiteModules.{u} (R₀.over U))) := derived_products
  have hBP : HasCountableProducts
      (DerivedCategory (ringedSiteModules.{u} (B₀.over U))) := derived_products
  have : G.mapDerivedCategory.IsRightAdjoint := scalarRestriction_derived_isRightAdjoint φU
  have : G.mapDerivedCategory.ReflectsIsomorphisms := derived_reflectsIso G
  let P := DerivedCategory.Q.objPreimage M
  let N := DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let eB : (localCoefficientDerivedRestriction B U).obj M ≅
      DerivedCategory.Q.obj ((TB.mapHomologicalComplex (.up ℤ)).obj P) :=
    ((localCoefficientDerivedRestriction B U).mapIso
      (DerivedCategory.Q.objObjPreimageIso M)).symm ≪≫ TB.mapDerivedCategoryFactors.app P
  let eR : (localCoefficientDerivedRestriction R U).obj N ≅
      DerivedCategory.Q.obj
        ((TR.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    TR.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let eC := scalar_slice_complex_iso R B φ U P
  let e : G.mapDerivedCategory.obj ((localCoefficientDerivedRestriction B U).obj M) ≅
      (localCoefficientDerivedRestriction R U).obj N :=
    G.mapDerivedCategory.mapIso eB ≪≫
      G.mapDerivedCategoryFactors.app ((TB.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
      DerivedCategory.Q.mapIso eC ≪≫ eR.symm
  let mB := (NatTrans.mapHomologicalComplex
    (localSectionMultiplicationNatTrans B U (φ.hom.app (op U) f)) (.up ℤ)).app P
  let mR := (NatTrans.mapHomologicalComplex
    (localSectionMultiplicationNatTrans R U f) (.up ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have heB : (localSectionDerivedMultiplication B U (φ.hom.app (op U) f)).app M ≫
      eB.hom = eB.hom ≫ DerivedCategory.Q.map mB := by
    dsimp only [eB, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    rw [← Category.assoc, ← NatTrans.naturality, Category.assoc]
    exact (congrArg
      (fun k ↦ (localCoefficientDerivedRestriction B U).map
        (DerivedCategory.Q.objObjPreimageIso M).inv ≫ k)
      (multiplication_fac B U (φ.hom.app (op U) f) P)).trans
      (Category.assoc _ _ _).symm
  have hm : (G.mapHomologicalComplex (.up ℤ)).map mB ≫ eC.hom = eC.hom ≫ mR :=
    scalar_complex_mul_commute R B φ U f P
  have he₁ : G.mapDerivedCategory.map
        ((localSectionDerivedMultiplication B U (φ.hom.app (op U) f)).app M) ≫
        G.mapDerivedCategory.map eB.hom =
      G.mapDerivedCategory.map eB.hom ≫ G.mapDerivedCategory.map (DerivedCategory.Q.map mB) := by
    simpa only [Functor.map_comp] using congrArg G.mapDerivedCategory.map heB
  have he₂ := G.mapDerivedCategoryFactors_hom_naturality mB
  have he₃ : DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map mB) ≫
      DerivedCategory.Q.map eC.hom = DerivedCategory.Q.map eC.hom ≫
        DerivedCategory.Q.map mR := by
    simpa only [Functor.map_comp] using congrArg DerivedCategory.Q.map hm
  have he₄ : DerivedCategory.Q.map mR ≫ eR.inv =
      eR.inv ≫ (localSectionDerivedMultiplication R U f).app N := by
    apply (cancel_mono eR.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show (localSectionDerivedMultiplication R U f).app N ≫ eR.hom =
      eR.hom ≫ DerivedCategory.Q.map mR from multiplication_fac R U f _]
    simp
  have he : G.mapDerivedCategory.map
      ((localSectionDerivedMultiplication B U (φ.hom.app (op U) f)).app M) ≫ e.hom =
      e.hom ≫ (localSectionDerivedMultiplication R U f).app N := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    exact commute_four he₁ he₂ he₃ he₄
  rw [completeElement_iff_towerIso J R N U f,
    completeElement_iff_towerIso J B M U (φ.hom.app (op U) f)]
  exact (towerIso_of_iso e _ _ he).symm.trans
    (towerIso_map_iff G.mapDerivedCategory
      (fun _ : ℕ ↦ (localCoefficientDerivedRestriction B U).obj M)
      (fun _ : ℕ ↦ (localSectionDerivedMultiplication B U
        (φ.hom.app (op U) f)).app M)).symm

end CategoryTheory
