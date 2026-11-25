/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulUnitZeroIso

/-! # The component normalization square for completed Koszul tensor augmentation

Source: Stacks Project, proetale.tex, Tag 099M, proof of lemma-naive-completion;
sites-cohomology.tex, Tag 06YN, the total tensor construction.
(blueprint: lem-weil-pbc-completed-koszul-tensor-augmentation-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

/-- Additivity of the recorded module tensor, with its coefficient sheaf explicit.
Source: Stacks 03EK (blueprint: lem-weil-pbc-completed-koszul-tensor-cone-comparison). -/
local instance augmentationComponentPreadditive
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalPreadditive (CompletedAdicModules T d) := by
  let : EssentiallySmall.{t + 1} T.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  exact SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)

attribute [local irreducible] completedAdicRing

private lemma singleTensorInv_f
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (Q : CompletedAdicModules T d) (p : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).inv.f p =
      P.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).inv ≫
        HomologicalComplex.ιTensorObj P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj Q) p 0 p (add_zero p) := by
  simp only [CochainComplex.mapBifunctorSingle₂Iso,
    CochainComplex.mapBifunctorSingle₁Iso,
    CochainComplex.mapBifunctorSingle₁XIso, Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_mk,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom,
    Functor.flip_map_app, curriedTensor_obj_map,
    ComplexShape.σ_def, mul_zero, Int.negOnePow_zero, one_smul, Category.assoc]

private lemma singleTensor_ι_hom
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (Q : CompletedAdicModules T d) (p : ℤ) :
    HomologicalComplex.ιTensorObj P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj Q) p 0 p (add_zero p) ≫
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom.f p =
      P.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom := by
  apply (cancel_epi
    (P.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).inv)).1
  erw [← Category.assoc, ← singleTensorInv_f T d,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
    ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
  rfl

@[reassoc] private lemma unitTensorInv_f
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K : CochainComplex (CompletedAdicModules T d) ℤ) (p : ℤ) :
    (λ_ K).inv.f p = (λ_ (K.X p)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d))).inv ▷ K.X p ≫
      HomologicalComplex.ιTensorObj (𝟙_ _) K 0 p p (zero_add p) := by
  exact HomologicalComplex.leftUnitor'_inv K p

@[reassoc] private lemma unitTensor_ι_hom
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K : CochainComplex (CompletedAdicModules T d) ℤ) (p : ℤ) :
    HomologicalComplex.ιTensorObj (𝟙_ _) K 0 p p (zero_add p) ≫
        (λ_ K).hom.f p =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d))).hom ▷ K.X p ≫ (λ_ (K.X p)).hom := by
  apply (cancel_epi ((λ_ (K.X p)).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (CompletedAdicModules T d))).inv ▷ K.X p)).1
  simp only [Category.assoc]
  erw [← unitTensorInv_f_assoc T d,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

private lemma quotientUnit_f
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p : ℤ) :
    (completedQuotientTensorUnit T d P n).f p =
      (ρ_ (P.X p)).inv ≫ P.X p ◁ reconstructionQuotientUnit T d n := by
  exact (reconstructionOrdinaryUnit_exists T d).exists.choose_spec (P.X p) n

private lemma quotientUnitComparison_f
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : CompletedAdicModules T d) :
    ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).inv ≫
        (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)).hom).f 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d))).hom ▷ Q ≫ (λ_ Q).hom := by
  erw [HomologicalComplex.comp_f, singleTensorInv_f T d]
  simp only [Category.assoc]
  erw [unitTensor_ι_hom_assoc T d]
  erw [← leftUnitor_naturality
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom]
  erw [← whisker_exchange_assoc
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (CompletedAdicModules T d))).hom
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom]
  erw [← whiskerLeft_comp_assoc ((𝟙_ (CochainComplex
    (CompletedAdicModules T d) ℤ)).X 0)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).inv
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  change 𝟙 ((𝟙_ (CompletedAdicModules T d)) ⊗ Q) ≫ (λ_ Q).hom =
    (𝟙 (𝟙_ (CompletedAdicModules T d))) ▷ Q ≫ (λ_ Q).hom
  rw [id_whiskerRight]

private lemma normalization_coefficient
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (n : ℕ)
    (bU : completedAdicKoszulTensor T d r a (𝟙_ _) n ⟶
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
        (𝟙_ _)).asFunctor.obj (op n))
    (huU : completedAdicKoszulTensorUnit T d r a (𝟙_ _) n ≫ bU =
      completedQuotientTensorUnit T d (𝟙_ _) n) :
    completedAdicKoszulUnitZero T d r a n ≫
        ((λ_ (completedAdicKoszul T d r a n)).inv ≫ bU ≫
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
            (completedAdicFiniteModule T d n) (𝟙_ _)).inv ≫
          (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (completedAdicFiniteModule T d n))).hom).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (completedAdicFiniteModule T d n)).hom =
      reconstructionQuotientUnit T d n := by
  let Q := completedAdicFiniteModule T d n
  let j := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).inv ≫
    (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)).hom
  have hj : j.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d))).hom ▷ Q ≫ (λ_ Q).hom :=
    quotientUnitComparison_f T d Q
  change completedAdicKoszulUnitZero T d r a n ≫
    ((λ_ (completedAdicKoszul T d r a n)).inv ≫ bU ≫ j).f 0 ≫ _ = _
  clear_value j
  have h := congrArg (fun z ↦ z.f 0) huU
  dsimp only [HomologicalComplex.comp_f, completedAdicKoszulTensorUnit,
    completedAdicKoszulTensorUnitF] at h
  erw [quotientUnit_f T d] at h
  simp only [Category.assoc] at h
  have h' := (cancel_epi (ρ_ ((𝟙_ (CochainComplex
    (CompletedAdicModules T d) ℤ)).X 0)).inv).1 h
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [unitTensorInv_f T d]
  simp only [Category.assoc]
  erw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, reassoc_of% h', hj,
    whisker_exchange_assoc]
  erw [← comp_whiskerRight_assoc
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (CompletedAdicModules T d))).inv
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (CompletedAdicModules T d))).hom (𝟙_ (CompletedAdicModules T d)),
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
    leftUnitor_naturality, Iso.inv_hom_id_assoc]

@[reassoc] private lemma tensorSummand_whiskerLeft
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P K L : CochainComplex (CompletedAdicModules T d) ℤ) (c : K ⟶ L)
    (p q k : ℤ) (h : p + q = k) :
    HomologicalComplex.ιTensorObj P K p q k h ≫ (P ◁ c).f k =
      P.X p ◁ c.f q ≫ HomologicalComplex.ιTensorObj P L p q k h := by
  change _ ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P) c
    (curriedTensor _) (.up ℤ)).f k = _
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map]
  exact Category.id_comp _

/-- Normalization determines the tensor square at one quotient level. The two given
maps are just maps of complexes; no naturality in P or in the quotient level is assumed.
The source comparison is tensor of the left unitor of the Koszul complex. The target
comparison first identifies the quotient tensor at the cochain unit with the quotient
in degree zero, and then uses the single-degree-zero total tensor comparison.

Source: Stacks Project, proetale.tex, proof of lemma-naive-completion (099M), finite
Koszul augmentation, and sites-cohomology.tex, Definition 06YN, total tensor.
(blueprint: lem-weil-pbc-completed-koszul-tensor-augmentation-component).

Proof: write K for the completed Koszul complex at n, Q for the finite quotient
module and U for the cochain tensor unit. Put
c = lambda_K^{-1} followed by bU followed by the displayed identification
of the ordinary quotient tensor of U with Q[0]. The degree-zero Koszul unit
u : O -> K^0 is invertible: exterior degree zero is the rank-one coefficient
module, constant realization identifies its unit, and scalar extension sends
the rank-one unit isomorphism to the rank-one unit isomorphism. The unit equation
for bU therefore gives u followed by c^0 equal to the quotient unit O -> Q.
In every nonzero degree the target Q[0] is zero, so c has zero component there.
Compare b with P tensor c followed by the single-degree-zero comparison. The
total summand inclusions jointly detect maps in each degree. On a (p,q) summand
with q nonzero the first map is zero by hz and the second by c^q = 0. On the
(p,0) summand precompose with the isomorphism P^p tensor u. The unit formula hu
for b and the just-established formula for c^0 give the same map
P^p -> P^p tensor Q, using naturality of the module right unitor. Cancel that
isomorphism and conclude equality. Whisker the resulting equality with tensor
of lambda_K and cancel its inverse. This gives exactly the displayed square.
All identifications are the existing single-complex isomorphisms, so the argument
applies to unbounded P, r=0, a unit ideal, the zero ring and the empty scheme. -/
theorem completedKoszulTensorAugmentationComponent
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (n : ℕ)
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (b : completedAdicKoszulTensor T d r a P n ⟶
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P).asFunctor.obj
        (op n))
    (bU : completedAdicKoszulTensor T d r a (𝟙_ _) n ⟶
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
        (𝟙_ _)).asFunctor.obj (op n))
    (hu : completedAdicKoszulTensorUnit T d r a P n ≫ b =
      completedQuotientTensorUnit T d P n)
    (hz : ∀ (p q : ℤ), q ≠ 0 →
      completedKoszulTensorSummand T d r a P n p q ≫ b.f (p + q) = 0)
    (huU : completedAdicKoszulTensorUnit T d r a (𝟙_ _) n ≫ bU =
      completedQuotientTensorUnit T d (𝟙_ _) n) :
    P ◁ bU ≫ (tensorLeft P).map
        ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (completedAdicFiniteModule T d n) (𝟙_ _)).inv ≫
            (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj
              (completedAdicFiniteModule T d n))).hom) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (completedAdicFiniteModule T d n) P).hom =
      P ◁ (λ_ (completedAdicKoszul T d r a n)).hom ≫ b := by
  let K := completedAdicKoszul T d r a n
  let Q := completedAdicFiniteModule T d n
  let j := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).inv ≫
    (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)).hom
  change P ◁ bU ≫ P ◁ j ≫
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom =
      P ◁ (λ_ K).hom ≫ b
  let c : K ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj Q :=
    (λ_ K).inv ≫ bU ≫ j
  have hc : completedAdicKoszulUnitZero T d r a n ≫ c.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom =
        reconstructionQuotientUnit T d n :=
    normalization_coefficient T d r a n bU huU
  have hi : IsIso (completedAdicKoszulUnitZero T d r a n) :=
    completedKoszulUnitZero_isIso T d r a n
  have hcdef : c = (λ_ K).inv ≫ bU ≫ j := rfl
  clear_value j c
  have hb : P ◁ c ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom = b := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = k at hpq
    by_cases hq : q = 0
    · subst q
      obtain rfl : k = p := by omega
      erw [HomologicalComplex.comp_f]
      change HomologicalComplex.ιTensorObj P K k 0 k (add_zero k) ≫
        (P ◁ c).f k ≫ _ = HomologicalComplex.ιTensorObj P K k 0 k (add_zero k) ≫ _
      erw [tensorSummand_whiskerLeft_assoc T d P K _ c k 0 k (add_zero k),
        singleTensor_ι_hom T d P Q k]
      apply (cancel_epi ((ρ_ (P.X k)).inv ≫
        P.X k ◁ completedAdicKoszulUnitZero T d r a n)).1
      simp only [Category.assoc, ← whiskerLeft_comp, hc]
      have h := congrArg (fun z ↦ z.f k) hu
      erw [HomologicalComplex.comp_f, quotientUnit_f T d P n k] at h
      exact h.symm
    · subst k
      erw [HomologicalComplex.comp_f]
      change HomologicalComplex.ιTensorObj P K p q (p + q) rfl ≫
        (P ◁ c).f (p + q) ≫ _ =
          HomologicalComplex.ιTensorObj P K p q (p + q) rfl ≫ _
      erw [tensorSummand_whiskerLeft_assoc T d P K _ c p q (p + q) rfl]
      have hcq : c.f q = 0 :=
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Q q hq).eq_of_tgt _ _
      erw [hcq, MonoidalPreadditive.whiskerLeft_zero, zero_comp]
      exact (hz p q hq).symm
  apply (cancel_epi (P ◁ (λ_ K).inv)).1
  rw [hcdef] at hb
  simpa only [Category.assoc, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp] using hb

end AlgebraicGeometry.Scheme
