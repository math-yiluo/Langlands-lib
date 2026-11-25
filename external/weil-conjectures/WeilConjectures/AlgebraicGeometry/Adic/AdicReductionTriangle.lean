/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # The completed coefficient reduction triangle

A normalized two-term resolution of a quotient ring sheaf gives a distinguished triangle
for every unbounded complex, with its actual derived scalar-extension unit as second arrow.
The same tensor calculation identifies the cokernel of the first arrow on cohomology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private def complexEndomorphism {C : Type*} [Category C] [Abelian C]
    (α : 𝟭 C ⟶ 𝟭 C) (P : CochainComplex C ℤ) : P ⟶ P where
  f i := α.app (P.X i)
  comm' i j _ := (α.naturality (P.d i j)).symm

private theorem complexEndomorphism_homology
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (α : 𝟭 C ⟶ 𝟭 C) (P : CochainComplex C ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor C q).map
        (DerivedCategory.Q.map (complexEndomorphism α P)) =
      α.app ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj P)) := by
  let e := (DerivedCategory.homologyFunctorFactors C q).app P
  apply (cancel_mono e.hom).mp
  dsimp only [e, Iso.app_hom]
  rw [DerivedCategory.homologyFunctorFactors_hom_naturality,
    HomologicalComplex.homologyMap_eq_app_homology α _ (fun _ ↦ rfl)]
  exact α.naturality e.hom

private theorem complexCounit_isIso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso (pbcComplexCounit φ P) := by
  have := pbcExtensionCounit_isIso φ P hP
  dsimp only [pbcComplexCounit]
  infer_instance

private theorem flat_model_triangle (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (α : 𝟭 (pbcModules T R) ⟶ 𝟭 (pbcModules T R))
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hzero : complexEndomorphism α P ≫
      (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P = 0)
    (hS : (ShortComplex.mk (complexEndomorphism α P)
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P)
      hzero).ShortExact) :
    ∃ w : (pbcDerivedRestrict φ).obj
        ((pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P)) ⟶
          (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
        (DerivedCategory.Q.map (complexEndomorphism α P))
        ((pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P)) w ∈
          distTriang _ := by
  have := complexCounit_isIso T φ P hP
  let e := (pbcDerivedRestrict φ).mapIso (asIso (pbcComplexCounit φ P)) ≪≫
    (pbcRestrict φ).mapDerivedCategoryFactors.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
  let w := e.hom ≫ DerivedCategory.triangleOfSESδ hS
  refine ⟨w, Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hS) _ ?_⟩
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · simp
  · change (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
        e.hom = 𝟙 _ ≫ _
    rw [Category.id_comp]
    exact (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec P hP
  · simp [w]

private theorem natural_resolution_triangle (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (α : 𝟭 (pbcModules T R) ⟶ 𝟭 (pbcModules T R))
    (hseq : ∀ M : pbcModules T R,
      exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory R) M) →
      ∃ h : α.app M ≫ (pbcScalarAdjunction φ).unit.app M = 0,
        (ShortComplex.mk (α.app M) ((pbcScalarAdjunction φ).unit.app M) h).ShortExact)
    (K : DerivedCategory (pbcModules T R)) :
    ∃ (a : K ⟶ K)
      (w : (pbcDerivedRestrict φ).obj ((pbcDerivedExtend φ).obj K) ⟶ K⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk a ((pbcDerivedScalarAdjunction φ).unit.app K) w ∈
        distTriang _ ∧ ∀ q : ℤ,
          (DerivedCategory.homologyFunctor _ q).map a =
            α.app ((DerivedCategory.homologyFunctor _ q).obj K) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  obtain ⟨P, r, hP, hflat, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) (DerivedCategory.Q.objPreimage K)
  let : QuasiIso r := hr
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map r) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hz : complexEndomorphism α P ≫
      (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P = 0 := by
    ext i : 1
    exact (hseq (P.X i) (hflat i)).choose
  have hS : (ShortComplex.mk (complexEndomorphism α P)
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P)
      hz).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact (hseq (P.X i) (hflat i)).choose_spec
  obtain ⟨wP, hTP⟩ := flat_model_triangle T φ α P hP hz hS
  let F := pbcDerivedExtend φ ⋙ pbcDerivedRestrict φ
  let eR := F.mapIso e
  let a := e.inv ≫ DerivedCategory.Q.map (complexEndomorphism α P) ≫ e.hom
  let w := eR.inv ≫ wP ≫ e.hom⟦(1 : ℤ)⟧'
  refine ⟨a, w, ?_, ?_⟩
  · apply Pretriangulated.isomorphic_distinguished _ hTP _
    refine Pretriangulated.Triangle.isoMk _ _ e.symm e.symm eR.symm ?_ ?_ ?_
    · simp [a]
    · change (pbcDerivedScalarAdjunction φ).unit.app K ≫ F.map e.inv =
        e.inv ≫ (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P)
      exact ((pbcDerivedScalarAdjunction φ).unit.naturality e.inv).symm
    · simp [w]
  · intro q
    let H := DerivedCategory.homologyFunctor (pbcModules T R) q
    change H.map a = α.app (H.obj K)
    dsimp only [a]
    rw [Functor.map_comp, Functor.map_comp, complexEndomorphism_homology]
    have hα := (α.naturality (H.map e.hom)).symm
    change α.app (H.obj (DerivedCategory.Q.obj P)) ≫ H.map e.hom =
      H.map e.hom ≫ α.app (H.obj K) at hα
    rw [hα, ← Category.assoc, ← H.map_comp, e.inv_hom_id,
      H.map_id, Category.id_comp]

namespace ReductionTensor
open SheafOfModules MonoidalCategory
open scoped ChangeOfRings
variable (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
  {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
attribute [local instance] WeilConjectures.instEssentiallySmallProEt_weilConjectures
attribute [local instance] WeilConjectures.sfAbSheafify
attribute [local instance] WeilConjectures.sfAbBijective
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private noncomputable def tensorUnitIso
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) :
    (siteSheafTensorRight (A := R) M).obj (unit ((adicLisseForget T).obj R)) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)).mapIso
      ((siteTensorRightIso R M.val).app (unit ((adicLisseForget T).obj R)).val ≪≫ λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj
      R).obj)).counit).app M

private noncomputable def restrictedSheafification
    (P : _root_.PresheafOfModules.{u + 1} ((adicLisseForget T).obj S).obj) :
    (PresheafOfModules.sheafification.{u + 1} (𝟙 ((adicLisseForget T).obj R).obj)).obj
      ((PresheafOfModules.restrictScalars.{u + 1} ((adicLisseForget T).map φ).hom).obj P) ⟶
      (restrictScalars.{u + 1} ((adicLisseForget T).map φ)).obj
        ((PresheafOfModules.sheafification.{u + 1} (𝟙 ((adicLisseForget T).obj S).obj)).obj P) := by
  refine (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (P := (PresheafOfModules.restrictScalars.{u + 1} ((adicLisseForget T).map φ).hom).obj P)
    (F := (restrictScalars.{u + 1} ((adicLisseForget T).map φ)).obj
      ((PresheafOfModules.sheafification.{u + 1} (𝟙 ((adicLisseForget T).obj S).obj)).obj P))
    (𝟙 ((adicLisseForget T).obj R).obj)).symm ?_
  exact (PresheafOfModules.restrictScalars.{u + 1} ((adicLisseForget T).map φ).hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj S).obj)).unit.app P)

attribute [local irreducible] restrictedSheafification

set_option backward.isDefEq.respectTransparency false in
private theorem restrictedSheafification_underlying
    (P : _root_.PresheafOfModules.{u + 1} ((adicLisseForget T).obj S).obj) :
    IsIso ((toSheaf ((adicLisseForget T).obj R)).map (restrictedSheafification T R φ P)) := by
  rw [restrictedSheafification,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  have h : (PresheafOfModules.toPresheaf ((adicLisseForget T).obj R).obj).map
      ((PresheafOfModules.restrictScalars ((adicLisseForget T).map φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj
          S).obj)).unit.app P)) =
      CategoryTheory.toSheafify (ProEt.topology T) P.presheaf := by
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 ((adicLisseForget T).obj S).obj) P
  let adj := CategoryTheory.sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1}
  change IsIso ((adj.homEquiv P.presheaf
    ((presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).obj P.presheaf)).symm
      (adj.unit.app P.presheaf))
  have hh := adj.homEquiv_symm_unit P.presheaf
  exact hh.symm ▸ IsIso.id _

private theorem restrictedSheafification_isIso
    (P : _root_.PresheafOfModules.{u + 1} ((adicLisseForget T).obj S).obj) :
    IsIso (restrictedSheafification T R φ P) := by
  have : IsIso ((toSheaf ((adicLisseForget T).obj R)).map (restrictedSheafification T R φ P)) :=
    restrictedSheafification_underlying T R φ P
  exact isIso_of_reflects_iso _ (toSheaf ((adicLisseForget T).obj R))

private noncomputable def tensorQuotientPresheafIso
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) :
    siteTensorPresheaf (R := R.obj)
        ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj
          S))).val M.val ≅
      (PresheafOfModules.restrictScalars ((adicLisseForget T).map φ).hom).obj
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · exact (LinearEquiv.refl (R.obj.obj V)
      (TensorProduct (R.obj.obj V)
        ((ModuleCat.restrictScalars (φ.hom.app V).hom).obj
          (ModuleCat.of (S.obj.obj V) (S.obj.obj V))) (M.val.obj V))).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro b x
    exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) b x).symm

private noncomputable def tensorQuotientIso
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) :
    (siteSheafTensorRight (A := R) M).obj
        ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj S))) ≅
      (restrictScalars ((adicLisseForget T).map φ)).obj (SheafOfModules.changeOfRings.{u, u + 1,
        u + 1} φ M) := by
  letI := restrictedSheafification_isIso T R φ (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u
    + 1} φ M)
  exact (PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)).mapIso
      (tensorQuotientPresheafIso T R φ M) ≪≫
    asIso (restrictedSheafification T R φ (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      φ M))

attribute [local irreducible] tensorUnitIso tensorQuotientPresheafIso tensorQuotientIso

set_option backward.isDefEq.respectTransparency false in
private theorem tensorUnitIso_unit
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (tensorUnitIso T R M).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj R).obj)).unit.app
        (siteTensorPresheaf (unit ((adicLisseForget T).obj R)).val M.val)).app V
          ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) = x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj R).obj)
  let f := ((siteTensorRightIso R M.val).app (unit ((adicLisseForget T).obj R)).val ≪≫ λ_ M.val).hom
  have hn := adj.unit.naturality f
  have ht := adj.right_triangle_components M
  have hn' := congrArg (fun g ↦ g.app V
    ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) hn
  have ht' := congrArg (fun g ↦ g.app V x) ht
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hn' ht'
  change (tensorUnitIso T R M).hom.val.app V _ = _
  simp only [tensorUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [← hn']
  have hf : f.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) = x := by
    change (1 : R.obj.obj V) • x = x
    exact one_smul _ _
  change (adj.counit.app M).val.app V ((adj.unit.app M.val).app V
    (f.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x))) = x
  rw [hf]
  exact ht'

private theorem tensorUnitIso_inv_apply
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (tensorUnitIso T R M).inv.val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj R).obj)).unit.app
        (siteTensorPresheaf (unit ((adicLisseForget T).obj R)).val M.val)).app V
          ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  apply_fun (tensorUnitIso T R M).hom.val.app V
  · have h := congrArg (fun g ↦ g.val.app V x) (tensorUnitIso T R M).inv_hom_id
    exact h.trans (tensorUnitIso_unit T R M V x).symm
  · intro a b hab
    have h := congrArg ((tensorUnitIso T R M).inv.val.app V) hab
    have hc := congrArg (fun g ↦ g.val.app V) (tensorUnitIso T R M).hom_inv_id
    have ha := ConcreteCategory.congr_hom hc a
    have hb := ConcreteCategory.congr_hom hc b
    exact ha.symm.trans (h.trans hb)

private theorem restrictedSheafification_unit
    (P : _root_.PresheafOfModules.{u + 1} ((adicLisseForget T).obj S).obj) (V : T.ProEtᵒᵖ) (x :
      P.obj V) :
    (restrictedSheafification T R φ P).val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj R).obj)).unit.app
        ((PresheafOfModules.restrictScalars ((adicLisseForget T).map φ).hom).obj P)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
        P).app V x := by
  unfold restrictedSheafification
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars ((adicLisseForget T).map φ).hom).obj P)
    (F := (restrictScalars ((adicLisseForget T).map φ)).obj
      ((PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj S).obj)).obj P))
    (𝟙 ((adicLisseForget T).obj R).obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars ((adicLisseForget T).map φ).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj S).obj)).unit.app P))
  have hh := congrArg (fun g ↦ g.app V x) h
  exact hh

variable
  (p : unit ((adicLisseForget T).obj R) ⟶
    (pbcRestrict φ).obj (unit ((adicLisseForget T).obj S)))
  (f : unit ((adicLisseForget T).obj R) ⟶ unit ((adicLisseForget T).obj R))

private noncomputable def quotientMorphism
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) :
    M ⟶ (restrictScalars ((adicLisseForget T).map φ)).obj (SheafOfModules.changeOfRings.{u, u +
      1, u + 1} φ M) :=
  (tensorUnitIso T R M).inv ≫ (siteSheafTensorRight (A := R) M).map
    p ≫ (tensorQuotientIso T R φ M).hom

set_option backward.isDefEq.respectTransparency false in
private theorem quotientMorphism_apply
    (hp : ∀ V : T.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (quotientMorphism T R φ p M).val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj R).obj)
  let g := siteTensorHom p.val M.val
  let k := (tensorQuotientPresheafIso T R φ M).hom
  have hg := congrArg (fun f ↦ f.app V
    ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) (adj.unit.naturality g)
  have hk := congrArg (fun f ↦ f.app V
    ((show ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj
      S))).val.obj V
      from (1 : S.obj.obj V)) ⊗ₜ[R.obj.obj V] x))
      (adj.unit.naturality k)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hg hk
  have hg1 : g.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) =
      ((show ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj
        S))).val.obj V
        from (1 : S.obj.obj V)) ⊗ₜ[R.obj.obj V] x) := by
    change (p.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x = _
    rw [hp V]
  change ((adj.unit.app _).app V) (g.app V _) = _ at hg
  rw [hg1] at hg
  simp only [quotientMorphism, comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [tensorUnitIso_inv_apply]
  change (tensorQuotientIso T R φ M).hom.val.app V
    ((PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)).map g |>.val.app V <|
      _) = _
  erw [← hg]
  simp only [tensorQuotientIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (restrictedSheafification T R φ (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    φ M)).val.app V
    (((PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)).map k).val.app V
      ((adj.unit.app (siteTensorPresheaf
        ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj
          S))).val M.val)).app V
        ((show ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj
          S))).val.obj V
          from (1 : S.obj.obj V)) ⊗ₜ[R.obj.obj V] x))) = _
  erw [← hk]
  have hk1 : k.app V
      ((show ((restrictScalars ((adicLisseForget T).map φ)).obj (unit ((adicLisseForget T).obj
        S))).val.obj V
        from (1 : S.obj.obj V)) ⊗ₜ[R.obj.obj V] x) =
      (1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x := by
    dsimp only [k]
    unfold tensorQuotientPresheafIso
    rfl
  change (restrictedSheafification T R φ (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    φ M)).val.app V
    ((adj.unit.app _).app V (k.app V _)) = _
  rw [hk1]
  exact restrictedSheafification_unit T R φ _ V _

private noncomputable def tensorMultiplication
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) : M ⟶ M :=
  (tensorUnitIso T R M).inv ≫ (siteSheafTensorRight (A := R) M).map
    f ≫ (tensorUnitIso T R M).hom

private local instance adicReductionUnitSectionSMul
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) (V : T.ProEtᵒᵖ) :
    SMul ((unit ((adicLisseForget T).obj R)).val.obj V) (M.val.obj V) :=
  inferInstanceAs (SMul (R.obj.obj V) (M.val.obj V))

set_option backward.isDefEq.respectTransparency false in
private theorem tensorMultiplication_apply
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (tensorMultiplication T R f M).val.app V x =
      f.val.app V (1 : R.obj.obj V) • x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((adicLisseForget T).obj R).obj)
  let g := siteTensorHom f.val M.val
  have hg := congrArg (fun f ↦ f.app V
    ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) (adj.unit.naturality g)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hg
  simp only [tensorMultiplication, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [tensorUnitIso_inv_apply]
  change (tensorUnitIso T R M).hom.val.app V
    ((PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)).map g |>.val.app V <|
      _) = _
  erw [← hg]
  change (tensorUnitIso T R M).hom.val.app V
    ((adj.unit.app (siteTensorPresheaf (unit ((adicLisseForget T).obj R)).val M.val)).app V
      ((f.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x)) = _
  have ht : (f.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x =
      (1 : R.obj.obj V) ⊗ₜ[R.obj.obj V]
        (f.val.app V (1 : R.obj.obj V) • x) := by
    have hh := TensorProduct.smul_tmul (R := R.obj.obj V) (R' := R.obj.obj V)
      (f.val.app V (1 : R.obj.obj V))
      (1 : R.obj.obj V) x
    simpa only [smul_eq_mul, mul_one] using hh
  rw [ht]
  exact tensorUnitIso_unit T R M V _

private noncomputable def ordinaryQuotientIso
    (M : pbcModules T R) :
    (siteSheafTensorRight (A := R) M).obj ((pbcRestrict φ).obj
        (unit ((adicLisseForget T).obj S))) ≅
      (pbcRestrict φ).obj ((pbcExtend φ).obj M) :=
  tensorQuotientIso T R φ M ≪≫ (pbcRestrict φ).mapIso
    (eqToIso ((pbcExtensionExistence φ).choose_spec.choose M)).symm

private theorem ordinaryUnit_apply (M : pbcModules T R) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((pbcScalarAdjunction φ).unit.app M).val.app V x = pbcTensorSection φ M V 1 x := by
  exact (pbcScalarAdjunction_exists φ).exists.choose_spec M V x

attribute [local irreducible] ordinaryQuotientIso pbcScalarAdjunction

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryQuotient_unit
    (hp : ∀ V : T.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (M : pbcModules T R) :
    (tensorUnitIso T R M).inv ≫ (siteSheafTensorRight (A := R) M).map p ≫
        (ordinaryQuotientIso T R φ M).hom =
      (pbcScalarAdjunction φ).unit.app M := by
  simp only [ordinaryQuotientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, eqToIso.inv, ← Category.assoc]
  ext V x
  change ((pbcRestrict φ).map (eqToHom
    ((pbcExtensionExistence φ).choose_spec.choose M).symm)).val.app V
      ((quotientMorphism T R φ p M).val.app V x) = _
  refine (congrArg (fun y ↦
    ((pbcRestrict φ).map (eqToHom
      ((pbcExtensionExistence φ).choose_spec.choose M).symm)).val.app V y)
        (quotientMorphism_apply T R φ p hp M V x)).trans ?_
  refine Eq.trans ?_ (ordinaryUnit_apply T R φ M V x).symm
  change (eqToHom ((pbcExtensionExistence φ).choose_spec.choose M).symm).val.app V
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app V
            ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) =
    (eqToHom ((pbcExtensionExistence φ).choose_spec.choose M).symm).val.app V
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x))
  congr 1

private noncomputable def multiplicationNatural : 𝟭 (pbcModules T R) ⟶ 𝟭 (pbcModules T R) where
  app M := tensorMultiplication T R f M
  naturality {M N} g := by
    ext V x
    change (tensorMultiplication T R f N).val.app V (g.val.app V x) =
      g.val.app V ((tensorMultiplication T R f M).val.app V x)
    rw [tensorMultiplication_apply, tensorMultiplication_apply]
    exact ((g.val.app V).hom.map_smul _ x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_complex_exact
    (hfp : f ≫ p = 0)
    (hS : (ShortComplex.mk f p hfp).ShortExact)
    (hp : ∀ V : T.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (M : pbcModules T R) :
    ∃ h : (multiplicationNatural T R f).app M ≫
        (pbcScalarAdjunction φ).unit.app M = 0,
      ((ShortComplex.mk (multiplicationNatural T R f |>.app M)
        ((pbcScalarAdjunction φ).unit.app M) h).Exact ∧
          Epi ((pbcScalarAdjunction φ).unit.app M)) ∧
      (exactFunctor _ _ (@tensorRight _ _ (monoidalCategory R) M) →
        (ShortComplex.mk (multiplicationNatural T R f |>.app M)
          ((pbcScalarAdjunction φ).unit.app M) h).ShortExact) := by
  let F := siteSheafTensorRight (A := R) M
  let := tensorLeft_additive_independent R M
  let : (tensorRight M).Additive := Functor.additive_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight M)
  let : F.Additive := Functor.additive_of_iso (siteSheafTensorRightIso R M).symm
  let e := tensorUnitIso T R M
  let eR := ordinaryQuotientIso T R φ M
  have hη := ordinaryQuotient_unit T R φ p hp M
  have hz : (multiplicationNatural T R f).app M ≫
      (pbcScalarAdjunction φ).unit.app M = 0 := by
    rw [← hη]
    change (e.inv ≫ F.map f ≫ e.hom) ≫ e.inv ≫ F.map p ≫ eR.hom = 0
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      hfp, Functor.map_zero, zero_comp, comp_zero]
  let S' := ShortComplex.mk ((multiplicationNatural T R f).app M)
    ((pbcScalarAdjunction φ).unit.app M) hz
  let i : (ShortComplex.mk f p hfp).map F ≅ S' :=
    ShortComplex.isoMk e e eR (by
      change e.hom ≫ (e.inv ≫ F.map f ≫ e.hom) = F.map f ≫ e.hom
      simp) (by
      change e.hom ≫ (pbcScalarAdjunction φ).unit.app M = F.map p ≫ eR.hom
      rw [← hη]
      simp only [e, eR, F, Iso.hom_inv_id_assoc])
  have hcol : PreservesFiniteColimits F := by
    let := tensorLeft_preservesColimits_independentCoefficients R M
    let : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
      preservesColimitsOfSize_shrink (tensorLeft M)
    let : PreservesFiniteColimits (tensorRight M) :=
      preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
    exact preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R M).symm
  have hepi := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1
    hcol _ hS
  have he : S'.Exact := (ShortComplex.exact_iff_of_iso i).1 hepi.1
  have hE : Epi S'.g := by
    have := hepi.2
    have hg : S'.g = e.inv ≫ F.map p ≫ eR.hom := hη.symm
    rw [hg]
    infer_instance
  refine ⟨hz, ⟨he, hE⟩, ?_⟩
  intro hflat
  have hF : exactFunctor _ _ F :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm hflat
  let := (exactFunctor_iff F).1 hF |>.1
  let := (exactFunctor_iff F).1 hF |>.2
  exact ShortComplex.shortExact_of_iso i (hS.map_of_exact F)

end ReductionTensor

/-- A normalized two-term quotient resolution induces the scalar-extension triangle.
Source: blueprint integral truncations, steps 1 and 3
(blueprint: lem-weil-pbc-adic-reduction-triangle).

Proof: tensor the coefficient sequence with a module. The tensor unit isomorphism and the
restriction/sheafification comparison identify its second arrow with the ordinary scalar
adjunction unit, using `p(1) = 1`. Tensor preserves cokernels, so the resulting sequence is
right exact for every module and short exact for a flat module. Choose a flat-term K-flat
representative of K. The degreewise short exact sequence yields a distinguished triangle;
the normalized K-flat counit identifies its second arrow with the derived unit. Transport
along the resolution isomorphism. Tensor multiplication is a natural endomorphism of the
identity, hence commutes with cohomology. Finally, right exactness identifies its cokernel
with ordinary scalar extension, with the displayed unit normalization.

The tensor/sheafification calculations adapt the private helpers of
`DerivedReductionResolutionIndependence`, without its unused sections-exact hypothesis.
The zero ring and empty site require no exception: all arguments use universal properties. -/
theorem pbc_adic_reduction_triangle
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S)
    (f : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      SheafOfModules.unit ((adicLisseForget T).obj R))
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S)))
    (hp : ∀ V : T.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (hzero : f ≫ p = 0) (hS : (ShortComplex.mk f p hzero).ShortExact)
    (K : DerivedCategory (pbcModules T R)) :
    ∃ (a : K ⟶ K)
      (w : (pbcDerivedRestrict φ).obj ((pbcDerivedExtend φ).obj K) ⟶ K⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk a ((pbcDerivedScalarAdjunction φ).unit.app K) w ∈
        distTriang _ ∧
      ∀ q : ℤ,
        let H := (DerivedCategory.homologyFunctor _ q).obj K
        (∃ e : H ≅ (SheafOfModules.siteSheafTensorRight
            (J := ProEt.topology T) (A := R) H).obj
              (SheafOfModules.unit ((adicLisseForget T).obj R)),
          (DerivedCategory.homologyFunctor _ q).map a ≫ e.hom =
            e.hom ≫ (SheafOfModules.siteSheafTensorRight
              (J := ProEt.topology T) (A := R) H).map f) ∧
        ∃ e : cokernel ((DerivedCategory.homologyFunctor _ q).map a) ≅
            (pbcRestrict φ).obj ((pbcExtend φ).obj H),
          cokernel.π ((DerivedCategory.homologyFunctor _ q).map a) ≫ e.hom =
            (pbcScalarAdjunction φ).unit.app H := by
  classical
  let α := ReductionTensor.multiplicationNatural T R f
  have hseq (M : pbcModules T R)
      (hflat : exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory R) M)) :
      ∃ h : α.app M ≫ (pbcScalarAdjunction φ).unit.app M = 0,
        (ShortComplex.mk (α.app M) ((pbcScalarAdjunction φ).unit.app M) h).ShortExact := by
    obtain ⟨hz, _, hs⟩ := ReductionTensor.tensor_complex_exact T R φ p f hzero hS hp M
    exact ⟨hz, hs hflat⟩
  obtain ⟨a, w, hT, ha⟩ := natural_resolution_triangle T φ α hseq K
  refine ⟨a, w, hT, ?_⟩
  intro q
  let H := (DerivedCategory.homologyFunctor (pbcModules T R) q).obj K
  refine ⟨?_, ?_⟩
  · let e := ReductionTensor.tensorUnitIso T R H
    refine ⟨e.symm, ?_⟩
    rw [ha q]
    change (e.inv ≫ _ ≫ e.hom) ≫ e.inv = e.inv ≫ _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [ha q]
    obtain ⟨hz, ⟨hex, hepi⟩, _⟩ :=
      ReductionTensor.tensor_complex_exact T R φ p f hzero hS hp H
    let v := cokernel.desc (α.app H) ((pbcScalarAdjunction φ).unit.app H) hz
    have : Mono v := hex.mono_cokernelDesc
    have : Epi (cokernel.π (α.app H) ≫ v) := by
      simpa only [v, cokernel.π_desc] using hepi
    have : Epi v := epi_of_epi (cokernel.π (α.app H)) v
    have : IsIso v := isIso_of_mono_of_epi v
    exact ⟨asIso v, cokernel.π_desc _ _ _⟩

end AlgebraicGeometry.Scheme
