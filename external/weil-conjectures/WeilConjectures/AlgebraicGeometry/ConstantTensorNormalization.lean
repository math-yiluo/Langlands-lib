/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantTensorSingle
import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones

/-! # Normalization determines a total tensor augmentation

Source: Stacks Project, Modules on Sites, Tag 03EK and proetale.tex, Tag 099M.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion.TensorComparison
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
attribute [local instance] TensorComparison.tensorTower_additive

attribute [local instance] flatConstantCochainMonoidal flatConstantCochainMonoidalStruct
  SheafOfModules.monoidalCategory
  Functor.preservesZeroMorphisms_of_additive

private lemma unitNormalization
    {B : Type*} [Category B] [MonoidalCategory B]
    {E V Q L T : B} (e : E ≅ 𝟙_ B) (d : T ≅ Q)
    (u : 𝟙_ B ⟶ V) (q : 𝟙_ B ⟶ Q)
    (i : E ⊗ V ⟶ L) (b : L ⟶ E ⊗ Q) (j : E ⊗ Q ⟶ T)
    (h : E ◁ u ≫ i ≫ b = E ◁ q)
    (hj : j ≫ d.hom = e.hom ▷ Q ≫ (λ_ Q).hom) :
    u ≫ (λ_ V).inv ≫ e.inv ▷ V ≫ i ≫ b ≫ j ≫ d.hom = q := by
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    reassoc_of% h, hj, whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, e.inv_hom_id, id_whiskerRight, Category.id_comp,
    leftUnitor_naturality, Iso.inv_hom_id_assoc]

section Generic
variable (B : Type*) [Category B] [Preadditive B] [HasZeroObject B]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [∀ (X Y : GradedObject ℤ B), GradedObject.HasTensor X Y]
  [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X : B, PreservesColimit (Functor.empty.{0} B) (tensorLeft X)]
  [∀ X : B, PreservesColimit (Functor.empty.{0} B) (tensorRight X)]

omit [∀ (X Y : GradedObject ℤ B), GradedObject.HasTensor X Y]
  [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X : B, PreservesColimit (Functor.empty.{0} B) (tensorLeft X)]
  [∀ X : B, PreservesColimit (Functor.empty.{0} B) (tensorRight X)] in
private lemma singleTensorInv_f
    (P : CochainComplex B ℤ)
    (Q : B) (p : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).inv.f p =
      P.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).inv ≫
        HomologicalComplex.ιTensorObj P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj Q) p 0 p (add_zero p) := by
  exact CochainComplex.mapBifunctorSingle₂Iso_inv_f (curriedTensor _) Q P p

omit [∀ (X Y : GradedObject ℤ B), GradedObject.HasTensor X Y]
  [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X : B, PreservesColimit (Functor.empty.{0} B) (tensorLeft X)]
  [∀ X : B, PreservesColimit (Functor.empty.{0} B) (tensorRight X)] in
private lemma singleTensor_ι_hom
    (P : CochainComplex B ℤ)
    (Q : B) (p : ℤ) :
    HomologicalComplex.ιTensorObj P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj Q) p 0 p (add_zero p) ≫
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom.f p =
      P.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom := by
  apply (cancel_epi
    (P.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).inv)).1
  erw [← Category.assoc, ← singleTensorInv_f B,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
    ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
  rfl

omit [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W] in
private lemma unitTensorInv_f
    (K : CochainComplex B ℤ) (p : ℤ) :
    (λ_ K).inv.f p = (λ_ (K.X p)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ B)).inv ▷ K.X p ≫
      HomologicalComplex.ιTensorObj (𝟙_ _) K 0 p p (zero_add p) := by
  exact HomologicalComplex.leftUnitor'_inv K p

omit [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W] in
private lemma unitTensor_ι_hom
    (K : CochainComplex B ℤ) (p : ℤ) :
    HomologicalComplex.ιTensorObj (𝟙_ _) K 0 p p (zero_add p) ≫
        (λ_ K).hom.f p =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ B)).hom ▷ K.X p ≫ (λ_ (K.X p)).hom := by
  apply (cancel_epi ((λ_ (K.X p)).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ B)).inv ▷ K.X p)).1
  simp only [Category.assoc]
  erw [← reassoc_of% (unitTensorInv_f B K p),
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

omit [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W] in
private lemma quotientUnitComparison_f
    (Q : B) :
    ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).inv ≫
        (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)).hom).f 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ B)).hom ▷ Q ≫ (λ_ Q).hom := by
  erw [HomologicalComplex.comp_f, singleTensorInv_f B]
  simp only [Category.assoc]
  erw [reassoc_of% (unitTensor_ι_hom B _ 0)]
  erw [← leftUnitor_naturality
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom]
  erw [← whisker_exchange_assoc
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ B)).hom
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom]
  erw [← whiskerLeft_comp_assoc ((𝟙_ (CochainComplex
    (B) ℤ)).X 0)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).inv
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

omit [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W] in
private lemma tensorSummand_whiskerLeft
    (P K L : CochainComplex B ℤ) (c : K ⟶ L)
    (p q k : ℤ) (h : p + q = k) :
    HomologicalComplex.ιTensorObj P K p q k h ≫ (P ◁ c).f k =
      P.X p ◁ c.f q ≫ HomologicalComplex.ιTensorObj P L p q k h := by
  change _ ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P) c
    (curriedTensor _) (.up ℤ)).f k = _
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map]
  exact Category.id_comp _

omit [∀ (X Y Z W : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X Y Z W] in
private lemma normalizedSummands
    (K P : CochainComplex B ℤ) (Q : B)
    (u : 𝟙_ B ⟶ K.X 0) [IsIso u] (q : 𝟙_ B ⟶ Q)
    (b : P ⊗ K ⟶ ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj P)
    (c : K ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj Q)
    (hc : u ≫ c.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom = q)
    (hu : ∀ p : ℤ,
      (ρ_ (P.X p)).inv ≫ P.X p ◁ u ≫
        HomologicalComplex.ιTensorObj P K p 0 p (add_zero p) ≫ b.f p =
          (ρ_ (P.X p)).inv ≫ P.X p ◁ q)
    (hz : ∀ p q : ℤ, q ≠ 0 →
      HomologicalComplex.ιTensorObj P K p q (p + q) rfl ≫ b.f (p + q) = 0) :
    P ◁ c ≫ (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom = b := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := K) (F := curriedTensor B) (c := .up ℤ)
  intro p q hpq
  change p + q = k at hpq
  by_cases hq : q = 0
  · subst q
    have hk : k = p := by omega
    revert hpq
    rw [hk]
    intro hpq
    erw [HomologicalComplex.comp_f]
    erw [reassoc_of% (tensorSummand_whiskerLeft B P K _ c p 0 p (add_zero p)),
      singleTensor_ι_hom B P Q p]
    apply (cancel_epi ((ρ_ (P.X p)).inv ≫ P.X p ◁ u)).1
    simp only [Category.assoc, ← whiskerLeft_comp, hc]
    exact (hu p).symm
  · subst k
    erw [HomologicalComplex.comp_f]
    erw [reassoc_of% (tensorSummand_whiskerLeft B P K _ c _ _ _ _)]
    have hcq : c.f q = 0 :=
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Q q hq).eq_of_tgt _ _
    erw [hcq, MonoidalPreadditive.whiskerLeft_zero, zero_comp]
    exact (hz p q hq).symm

private lemma normalizedSquareCore
    (K P : CochainComplex B ℤ) (Q : B)
    (u : 𝟙_ B ⟶ K.X 0) [IsIso u] (q : 𝟙_ B ⟶ Q)
    (b : P ⊗ K ⟶ ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj P)
    (bU : (𝟙_ (CochainComplex B ℤ)) ⊗ K ⟶
      ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex B ℤ)))
    (hu : ∀ p : ℤ,
      (ρ_ (P.X p)).inv ≫ P.X p ◁ u ≫
        HomologicalComplex.ιTensorObj P K p 0 p (add_zero p) ≫ b.f p =
          (ρ_ (P.X p)).inv ≫ P.X p ◁ q)
    (huU : ∀ p : ℤ,
      (ρ_ ((𝟙_ (CochainComplex B ℤ)).X p)).inv ≫ (𝟙_ (CochainComplex B ℤ)).X p ◁ u ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex B ℤ)) K p 0 p (add_zero p) ≫ bU.f p =
          (ρ_ ((𝟙_ (CochainComplex B ℤ)).X p)).inv ≫ (𝟙_ (CochainComplex B ℤ)).X p ◁ q)
    (hz : ∀ p q : ℤ, q ≠ 0 →
      HomologicalComplex.ιTensorObj P K p q (p + q) rfl ≫ b.f (p + q) = 0) :
    P ◁ bU ≫ P ◁
      ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).inv ≫
        (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)).hom) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom = P ◁ (λ_ K).hom ≫ b := by
  let j := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).inv ≫
    (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)).hom
  change P ◁ bU ≫ P ◁ j ≫
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom =
      P ◁ (λ_ K).hom ≫ b
  have hj : j.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)).hom ▷ Q ≫
        (λ_ Q).hom := quotientUnitComparison_f B Q
  clear_value j
  let c : K ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj Q :=
    (λ_ K).inv ≫ bU ≫ j
  have hcdef : c = (λ_ K).inv ≫ bU ≫ j := rfl
  clear_value c
  have hc : u ≫ c.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom = q := by
    have h := (cancel_epi (ρ_ ((𝟙_ (CochainComplex B ℤ)).X 0)).inv).1 (huU 0)
    rw [hcdef]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [unitTensorInv_f B]
    simp only [Category.assoc]
    exact unitNormalization
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q) u q _ _ _ h hj
  have hb : P ◁ c ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom = b := by
    exact normalizedSummands B K P Q u q b c hc hu hz
  apply (cancel_epi (P ◁ (λ_ K).inv)).1
  rw [hcdef] at hb
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp] using hb

end Generic

/-- Degree-zero normalization and vanishing away from that degree determine the
square relating a tensor augmentation to its value at the cochain unit.

Source: Stacks 099M, tensoring the finite augmentation, with Stacks 03EK.
(auxiliary; not a blueprint node).

Proof: transport bU along the left unitor and the single-factor comparison to a
map c from K to Q[0]. Its degree-zero map composed with u is q, by the normalization
at the unit and the unitor equations. On a (p,0) summand, cancel the isomorphism
P^p tensor u; the normalization of b and c makes the two maps equal. On every
(p,q) summand with q nonzero, the component of c vanishes because its target is
zero, and the component of b vanishes by hypothesis. Total tensor inclusions
jointly detect equality. Finally cancel the left unitor to recover the square.
No boundedness of P or K is used. -/
theorem normalizedTensorSquare
    (O : Sheaf J CommRingCat.{u}) (K P : Cx O) (Q : Mod O)
    (u : 𝟙_ (Mod O) ⟶ K.X 0) [IsIso u] (q : 𝟙_ (Mod O) ⟶ Q)
    (b : P ⊗ K ⟶ ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj P)
    (bU : (𝟙_ (Cx O)) ⊗ K ⟶
      ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ (Cx O)))
    (hu : ∀ p : ℤ,
      (ρ_ (P.X p)).inv ≫ P.X p ◁ u ≫
        HomologicalComplex.ιTensorObj P K p 0 p (add_zero p) ≫ b.f p =
          (ρ_ (P.X p)).inv ≫ P.X p ◁ q)
    (huU : ∀ p : ℤ,
      (ρ_ ((𝟙_ (Cx O)).X p)).inv ≫ (𝟙_ (Cx O)).X p ◁ u ≫
        HomologicalComplex.ιTensorObj (𝟙_ (Cx O)) K p 0 p (add_zero p) ≫ bU.f p =
          (ρ_ ((𝟙_ (Cx O)).X p)).inv ≫ (𝟙_ (Cx O)).X p ◁ q)
    (hz : ∀ p q : ℤ, q ≠ 0 →
      HomologicalComplex.ιTensorObj P K p q (p + q) rfl ≫ b.f (p + q) = 0) :
    P ◁ bU ≫ (quotientTensorIso J O Q P).hom = P ◁ (λ_ K).hom ≫ b := by
  unfold quotientTensorIso quotientUnitIso
  exact normalizedSquareCore (Mod O) K P Q u q b bU hu huU hz

end CategoryTheory.ConstantCompletion.TensorComparison
