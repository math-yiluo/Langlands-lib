/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Homology.HomTensorDifferential
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorNaturality

/-! # Normalized currying on K-flat complex representatives

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 0A90 and 0A96.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.KFlatRHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
set_option hygiene false in
set_option quotPrecheck false in
local notation "K" => CochainComplex A ℤ

/-- The existing predicate and its full subcategory; no resolution is chosen.
Source: Stacks 0A96 (auxiliary; not a blueprint node). -/
abbrev flat : ObjectProperty K := fun P ↦ P.IsKFlatTensor

variable [HasDerivedCategory.{w} A]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Der" => DerivedCategory A

/-- The actual functorial K-injective replacement used by derived internal Hom.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
abbrev resolution : K ⥤ K :=
  haveI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  CochainComplex.kInjectiveResolutionFunctor.{u} A

/-- Its actual coaugmentation.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
abbrev toResolution : 𝟭 K ⟶ resolution R :=
  haveI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  CochainComplex.toKInjectiveResolution.{u} A

/-- The localization factorization, fixing the representative comparison uniquely.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
def representativeIso :
    (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ derivedInternalHom J R ≅
      (𝟭 Kᵒᵖ).prod (resolution R) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q := by
  letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  exact Localization.fac _
    (derivedInternalHom_inverts J R (resolution R) (toResolution R) (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)

/-- Chain-level currying fixed by evaluation on pure tensors.
Source: Stacks 0A90 (auxiliary; not a blueprint node). -/
def chainIso (P L M : K) :
    letI := SheafOfModules.monoidalCategory R
    homComplex (R := R) P (homComplex (R := R) L M) ≅
      homComplex (R := R) (CochainComplex.mapBifunctor P L (curriedTensor A)) M := by
  let := SheafOfModules.monoidalCategory R
  have (n : ℤ) : IsIso (homTensorDegreewiseMap R P L M n) :=
    (homTensorDegreewiseMap_spec R P L M n).2
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (homTensorDegreewiseMap R P L M n))
    (fun n m _ ↦ homTensorDegreewiseMap_comm R P L M n m)

/-- The actual total tensor bifunctor.
Source: Stacks 0A90 (auxiliary; not a blueprint node). -/
abbrev total : K × K ⥤ K :=
  letI := SheafOfModules.monoidalCategory R
  Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- Iterated derived internal Hom on two K-flat representatives and a derived target.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
def left : (flat R).FullSubcategoryᵒᵖ × ((flat R).FullSubcategoryᵒᵖ × Der) ⥤ Der :=
  let a := CategoryTheory.Prod.fst (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × Der) ⋙ (flat R).ι.op ⋙ DerivedCategory.Q.op
  let b := CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × Der) ⋙
    CategoryTheory.Prod.fst (flat R).FullSubcategoryᵒᵖ Der ⋙
    (flat R).ι.op ⋙ DerivedCategory.Q.op
  let c := CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × Der) ⋙ CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ Der
  a.prod' (b.prod' c ⋙ derivedInternalHom J R) ⋙ derivedInternalHom J R

/-- Derived internal Hom from the ordinary total tensor of the representatives.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
def right : (flat R).FullSubcategoryᵒᵖ × ((flat R).FullSubcategoryᵒᵖ × Der) ⥤ Der :=
  let a := CategoryTheory.Prod.fst (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × Der) ⋙ (flat R).ι.op
  let b := CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × Der) ⋙
    CategoryTheory.Prod.fst (flat R).FullSubcategoryᵒᵖ Der ⋙ (flat R).ι.op
  let c := CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × Der) ⋙ CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ Der
  let t := a.prod' b ⋙ (prodOpEquiv K (D := K)).inverse ⋙ (total R).op ⋙
    DerivedCategory.Q.op
  t.prod' c ⋙ derivedInternalHom J R

/-- Restrict the derived target variable to complexes.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
abbrev representativeFunctor :
    (flat R).FullSubcategoryᵒᵖ × ((flat R).FullSubcategoryᵒᵖ × K) ⥤
      (flat R).FullSubcategoryᵒᵖ × ((flat R).FullSubcategoryᵒᵖ × Der) :=
  (𝟭 _).prod ((𝟭 _).prod DerivedCategory.Q)

/-- Comparison with an already K-injective target, using the coaugmentation.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
def injectiveRepresentativeIso {S : Type*} [Category S] (G : S ⥤ Kᵒᵖ × K)
    (hG : ∀ X, (G.obj X).2.IsKInjective) :
    G ⋙ (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ derivedInternalHom J R ≅
      G ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q := by
  letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let H := Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q
  let α := Functor.whiskerLeft G
    (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Kᵒᵖ)) (toResolution R)) H)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : ((G.obj X).2).IsKInjective := hG X
    have : ((resolution R).obj (G.obj X).2).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A _
    have : QuasiIso ((toResolution R).app (G.obj X).2) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_map (I' := (G.obj X).2)
      (I := (resolution R).obj (G.obj X).2) ((toResolution R).app (G.obj X).2)
      (𝟙 (G.obj X).1.unop)
  exact Functor.isoWhiskerLeft G (representativeIso R) ≪≫ (asIso α).symm

omit [HasDerivedCategory A] in
/-- Naturality of the evaluation-normalized chain currying.
Source: Stacks 0A90 (auxiliary; not a blueprint node).
Proof: Apply degreewise naturality and the extensionality of chain maps. -/
theorem chainIso_natural (P P' L L' M M' : K)
    (f : P' ⟶ P) (g : L' ⟶ L) (h : M ⟶ M') :
    letI := SheafOfModules.monoidalCategory R
    (((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op P')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h) ≫
        (chainIso R P' L' M').hom =
      (chainIso R P L M).hom ≫
        (((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).op).app M) ≫
        ((homComplexFunctor (R := R)).obj
          (op (CochainComplex.mapBifunctor P' L' (curriedTensor A)))).map h := by
  let := SheafOfModules.monoidalCategory R
  apply HomologicalComplex.hom_ext
  intro n
  exact (homTensorDegreewiseMap_natural R P P' L L' M M' f g h n).trans
    (Category.assoc _ _ _).symm

-- Descent combines large tensor and localization comparison terms.
set_option backward.isDefEq.respectTransparency true in
/-- The chain-representative comparison before descent in the target variable.
It is fixed by localization factorization and pure-tensor evaluation.
Source: Stacks 08J9, 0A90 and 0A96
(auxiliary; not a blueprint node). -/
@[irreducible] def representativeCurryIso :
    representativeFunctor R ⋙ left R ≅ representativeFunctor R ⋙ right R := by
  let := SheafOfModules.monoidalCategory R
  let S := (flat R).FullSubcategoryᵒᵖ × ((flat R).FullSubcategoryᵒᵖ × K)
  let a := CategoryTheory.Prod.fst (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × K) ⋙ (flat R).ι.op
  let b := CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × K) ⋙
    CategoryTheory.Prod.fst (flat R).FullSubcategoryᵒᵖ K ⋙ (flat R).ι.op
  let c := CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ
    ((flat R).FullSubcategoryᵒᵖ × K) ⋙ CategoryTheory.Prod.snd (flat R).FullSubcategoryᵒᵖ K
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  let F := derivedInternalHom.{u, w} J R
  let Q : K ⥤ Der := DerivedCategory.Q
  let inner := (b.prod' (c ⋙ resolution R)) ⋙ H
  have hinner (X : S) : (inner.obj X).IsKInjective := by
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    have : ((resolution R).obj X.2.2).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A _
    exact CochainComplex.isKInjective_homComplex_of_isKFlat
      X.2.1.unop.obj ((resolution R).obj X.2.2) X.2.1.unop.property
  let eInner : (b.prod' c) ⋙ (Q.op.prod Q) ⋙ F ≅ inner ⋙ Q :=
    Functor.isoWhiskerLeft (b.prod' c) (representativeIso R)
  let eLeft₁ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Functor.diag S)
      (NatIso.prod (Iso.refl (a ⋙ Q.op)) eInner)) F
  let eLeft₂ := injectiveRepresentativeIso R (a.prod' inner) hinner
  let eLeft : (a ⋙ Q.op).prod' ((b.prod' c) ⋙ (Q.op.prod Q) ⋙ F) ⋙ F ≅
      (a.prod' inner) ⋙ H ⋙ Q := eLeft₁ ≪≫ eLeft₂
  let tensor := (a.prod' b) ⋙ (prodOpEquiv K (D := K)).inverse ⋙ (total R).op
  let eRight : (tensor ⋙ Q.op).prod' (c ⋙ Q) ⋙ F ≅
      (tensor.prod' (c ⋙ resolution R)) ⋙ H ⋙ Q :=
    Functor.isoWhiskerLeft (tensor.prod' c) (representativeIso R)
  have tensor_map (K₁ K₂ L₁ L₂ : K) (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
      (total R).map (X := (K₁, K₂)) (Y := (L₁, L₂)) (f, g) =
        HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
    change HomologicalComplex.mapBifunctorMap f (𝟙 K₂) (curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 L₁) g (curriedTensor A) (.up ℤ) = _
    simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
  let eChain : (a.prod' inner) ⋙ H ≅ (tensor.prod' (c ⋙ resolution R)) ⋙ H :=
    NatIso.ofComponents
      (fun X ↦ chainIso R X.1.unop.obj X.2.1.unop.obj ((resolution R).obj X.2.2))
      (fun {X Y} f ↦ by
        change
          ((((homComplexFunctor (R := R)).map f.1.unop.hom.op).app
            (homComplex (R := R) X.2.1.unop.obj ((resolution R).obj X.2.2))) ≫
              ((homComplexFunctor (R := R)).obj (op Y.1.unop.obj)).map
                ((((homComplexFunctor (R := R)).map f.2.1.unop.hom.op).app
                  ((resolution R).obj X.2.2)) ≫
                    ((homComplexFunctor (R := R)).obj (op Y.2.1.unop.obj)).map
                      ((resolution R).map f.2.2))) ≫
            (chainIso R Y.1.unop.obj Y.2.1.unop.obj ((resolution R).obj Y.2.2)).hom =
          (chainIso R X.1.unop.obj X.2.1.unop.obj ((resolution R).obj X.2.2)).hom ≫
            ((((homComplexFunctor (R := R)).map
              ((total R).map
                  (X := (Y.1.unop.obj, Y.2.1.unop.obj))
                  (Y := (X.1.unop.obj, X.2.1.unop.obj))
                  (f.1.unop.hom, f.2.1.unop.hom)).op).app ((resolution R).obj X.2.2)) ≫
                ((homComplexFunctor (R := R)).obj
                  (op (HomologicalComplex.mapBifunctor Y.1.unop.obj Y.2.1.unop.obj
                    (MonoidalCategory.curriedTensor A) (.up ℤ)))).map ((resolution R).map f.2.2))
        rw [tensor_map]
        exact (Category.assoc _ _ _).trans
          (chainIso_natural R
          X.1.unop.obj Y.1.unop.obj X.2.1.unop.obj Y.2.1.unop.obj
          ((resolution R).obj X.2.2) ((resolution R).obj Y.2.2)
          f.1.unop.hom f.2.1.unop.hom ((resolution R).map f.2.2)))
  exact eLeft ≪≫ Functor.isoWhiskerRight eChain Q ≪≫ eRight.symm

/-- Canonical derived currying, obtained by the fully faithful localization descent.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
@[irreducible] def curryIso : left R ≅ right R :=
  (Localization.fullyFaithfulWhiskeringLeft (representativeFunctor R)
    ((MorphismProperty.isomorphisms (flat R).FullSubcategoryᵒᵖ).prod
      ((MorphismProperty.isomorphisms (flat R).FullSubcategoryᵒᵖ).prod
        (HomologicalComplex.quasiIso A (.up ℤ)))) Der).preimageIso
    (representativeCurryIso R)

end CategoryTheory.KFlatRHom
