/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.Monoidal.Dual

/-! # Normalization of the Hom unit for ordinary ringed-site complexes

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
open CategoryTheory.Functor.LaxMonoidal
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
variable (O : Sheaf J CommRingCat.{u})

attribute [local irreducible] homComplexFunctor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance ringedHomTensorUnitMonoidalPreadditive : MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

local instance ringedHomTensorUnitHasColimitsOfSize : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

attribute [local instance] ringedComplexClosed

private theorem sheaf_unit (A : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :
    MonoidalClosed.curry (λ_ A).hom ≫ (SheafOfModules.homObjUnitIso (R := O) A).hom =
      𝟙 A := by
  let S := PresheafOfModules.sheafification.{u}
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj))
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj))
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  have hε : ε S = inv (adj.counit.app U) := by
    change (SheafOfModules.sheafificationObjUnitIso O).inv = _
    simp only [SheafOfModules.sheafificationObjUnitIso, Iso.app_inv,
      asIso_inv, NatIso.isIso_inv_app]
    rfl
  have hm : (SheafOfModules.tensorObjIsoSheafification U A).inv ≫ (λ_ A).hom =
      S.map (λ_ A.val).hom ≫ adj.counit.app A := by
    rw [Iso.inv_comp_eq]
    simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
      tensorIso_inv, Iso.app_inv, asIso_inv, NatIso.isIso_inv_app,
      Functor.Monoidal.μIso_hom]
    rw [tensorHom_def']
    simp only [Category.assoc]
    change (λ_ A).hom = U ◁ inv (adj.counit.app A) ≫
      inv (adj.counit.app U) ▷ S.obj A.val ≫ μ S U.val A.val ≫
        S.map (λ_ A.val).hom ≫ adj.counit.app A
    rw [← hε]
    erw [← Functor.LaxMonoidal.left_unitality_assoc S A.val]
    erw [leftUnitor_naturality_assoc]
    simp
  have hc : MonoidalClosed.curry (λ_ A).hom =
      SheafOfModules.tensorHomEquiv U A A (λ_ A).hom := by
    apply MonoidalClosed.uncurry_injective
    erw [MonoidalClosed.uncurry_curry]
  rw [hc]
  apply SheafOfModules.hom_ext
  change PresheafOfModules.homObjEquiv U.val A.val A.val
    (adj.homEquiv _ A ((SheafOfModules.tensorObjIsoSheafification U A).inv ≫ (λ_ A).hom)) ≫
      (PresheafOfModules.homObjUnitIso A.val).hom = 𝟙 A.val
  rw [hm]
  erw [← Adjunction.homEquiv_counit adj, Equiv.apply_symm_apply]
  ext V x
  change (λ_ A.val).hom.app V
    ((1 : O.obj.obj V) ⊗ₜ[O.obj.obj V] A.val.map (𝟙 V) x) = x
  simp only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
    PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply]
  erw [PresheafOfModules.leftUnitor_hom_app (R := O.obj),
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply (R := O.obj.obj V)]
  simp

private theorem closed_unit_precomp {D : Type v} [Category.{w} D]
    [MonoidalCategory D] [MonoidalClosed D] {A K : D} (e : A ≅ 𝟙_ D)
    (g : A ⊗ K ⟶ K) (h : e.inv ▷ K ≫ g = (λ_ K).hom)
    (v : (ihom (𝟙_ D)).obj K ⟶ K)
    (hv : MonoidalClosed.curry (λ_ K).hom ≫ v = 𝟙 K) :
    MonoidalClosed.curry g ≫ (MonoidalClosed.pre e.inv).app K ≫ v = 𝟙 K := by
  rw [MonoidalClosed.curry_pre_app_assoc, h]
  exact hv

private theorem sheaf_curry_unit
    (A K : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (e : A ≅ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (g : A ⊗ K ⟶ K) (h : e.inv ▷ K ≫ g = (λ_ K).hom) :
    MonoidalClosed.curry g ≫ SheafOfModules.homObjMap (R := O) e.inv (𝟙 K) ≫
      (SheafOfModules.homObjUnitIso (R := O) K).hom = 𝟙 K := by
  have h' := closed_unit_precomp e g h
    (SheafOfModules.homObjUnitIso (R := O) K).hom (sheaf_unit O K)
  erw [SheafOfModules.pre_app (R := O) e.inv K] at h'
  exact h'

private theorem complex_curry_unit (P N : ringedSiteComplex O)
    (e : P.X 0 ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (g : P ⊗ N ⟶ N) (n : ℤ)
    (hi : e.inv ▷ N.X n ≫ HomologicalComplex.ιTensorObj P N 0 n n (zero_add n) ≫
      g.f n = (λ_ (N.X n)).hom) :
    (MonoidalClosed.curry g).f n ≫
      (homComplexπ P N n 0 n (zero_add n) ≫
        SheafOfModules.homObjMap (R := O) e.inv (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso (R := O) (N.X n)).hom) = 𝟙 (N.X n) := by
  have hc := ringedComplexCurry_component O g n 0 n (zero_add n)
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hc
  have hb := sheaf_curry_unit O (P.X 0) (N.X n) e
    (HomologicalComplex.ιTensorObj P N 0 n n (zero_add n) ≫ g.f n) hi
  have ht := congrArg (fun z : N.X n ⟶
      SheafOfModules.homObj (R := O) (P.X 0) (N.X n) ↦
        z ≫ SheafOfModules.homObjMap (R := O) e.inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := O) (N.X n)).hom) hc
  exact (Category.assoc ((MonoidalClosed.curry g).f n)
    (homComplexπ P N n 0 n (zero_add n))
    (SheafOfModules.homObjMap (R := O) e.inv (𝟙 _) ≫
      (SheafOfModules.homObjUnitIso (R := O) (N.X n)).hom)).symm.trans (ht.trans hb)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
private theorem unit_evaluation_f (N : ringedSiteComplex O) (n : ℤ) :
    (ringedHomUnitEvaluationIso O N).hom.f n = homComplexUnitEvaluation J O N n := rfl

attribute [local irreducible] ringedHomUnitEvaluationIso

/-- Transposing the tensor left unitor gives inverse evaluation at one.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Hom complexes and
its tensor-Hom adjunction; sites-modules.tex, internal Hom from the ring sheaf.
(auxiliary; not a blueprint node).

Proof: project to source degree zero. The signed comparison between the two
Hom conventions has sign (-1)^(0*n)=1 on this component. The tensor left unitor
on the (0,n) summand is multiplication of a section of the ring sheaf with a
section of N^n, after the canonical single-complex identification. Its transpose
sends a section y to the localized linear map a ↦ a*y. Evaluation at one returns y.
Conversely every localized linear map out of the rank-one unit is determined by
its value at one, so this transpose is inverse to evaluation. In other source
degrees the source unit complex is zero and the Hom component is zero. The Hom
product universal property therefore proves equality of the degree maps, hence
of the chain maps. No boundedness condition on N is used. -/
theorem ringedComplexHomUnit_eq (N : ringedSiteComplex O) :
    ringedComplexHomUnit O N = (ringedHomUnitEvaluationIso O N).inv := by
  rw [ringedComplexHomUnit_eq_curry]
  apply (cancel_mono (ringedHomUnitEvaluationIso O N).hom).mp
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, unit_evaluation_f, HomologicalComplex.id_f]
  let U := 𝟙_ (ringedSiteComplex O)
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
  change (MonoidalClosed.curry (λ_ N).hom).f n ≫
      (homComplexπ U N n 0 n (by omega) ≫
        SheafOfModules.homObjMap (R := O) e.inv (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso (R := O) (N.X n)).hom) = 𝟙 (N.X n)
  have hi : e.inv ▷ N.X n ≫ HomologicalComplex.ιTensorObj U N 0 n n (zero_add n) ≫
      (λ_ N).hom.f n = (λ_ (N.X n)).hom := by
    apply (cancel_epi (λ_ (N.X n)).inv).mp
    rw [Iso.inv_hom_id]
    have hu := congrArg (fun f : N ⟶ N ↦ f.f n) (λ_ N).inv_hom_id
    simpa only [e, U, HomologicalComplex.comp_f, CochainComplex.leftUnitor_inv_f,
      HomologicalComplex.id_f, Category.assoc] using hu
  exact complex_curry_unit O U N e (λ_ N).hom n hi

end CategoryTheory
