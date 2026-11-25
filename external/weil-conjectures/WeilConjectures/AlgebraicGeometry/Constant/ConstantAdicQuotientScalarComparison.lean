/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import all WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import Mathlib.RingTheory.AdicCompletion.Completeness
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.CategoryTheory.Exact.ExactScalarMatePasting

/-! # Constants and algebraic quotient restriction

Source: Stacks Tags 093J, 031C and 06YY.
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The actual map from a finite quotient to the corresponding completion quotient.
Source: Stacks Tag 031C
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicQuotientMap {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ (n + 1) →+*
      AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (algebraMap A (AdicCompletion I A))) (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx)

/-- Constant modules over a completion quotient, with their original finite-ring action.
Source: Stacks Tags 093J and 031C
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicQuotientModules (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal n) ⋙
    adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1)) ⋙
      pbcRestrict (pbcLevelConstantComparison X d n).inv

instance constantAdicQuotientModules_additive (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (constantAdicQuotientModules X d n).Additive := by
  have := CompletedConstantReduction.constant_additive X (A ⧸ d.ideal ^ (n + 1))
  unfold constantAdicQuotientModules
  infer_instance

instance constantAdicQuotientModules_limits (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteLimits (constantAdicQuotientModules X d n) := by
  have := (constantAdicFinite_constant_exact X (A ⧸ d.ideal ^ (n + 1))).1
  unfold constantAdicQuotientModules
  infer_instance

instance constantAdicQuotientModules_colimits (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteColimits (constantAdicQuotientModules X d n) := by
  have := (constantAdicFinite_constant_exact X (A ⧸ d.ideal ^ (n + 1))).2
  unfold constantAdicQuotientModules
  infer_instance

/-- Exact constants with precisely the inverse-image finite coefficient ring.
Source: Stacks Tags 093J and 03DA
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicQuotientRealization {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  (constantAdicQuotientModules X d n).mapDerivedCategory ⋙
    adicTowerPullback g ((pbcAdicRings X d).obj (op n))

/-- Constant sections in the concrete constant-module sheafification.
Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicModuleSection (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (N : ModuleCat.{u + 1} B) (V : X.ProEtᵒᵖ) (x : N) :
    ((adicLisseConstantModules X B).obj N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit X B)).unit.app
    ((siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))).obj N)).app V x

/-- Localize and pull back an ordinary restriction comparison. This construction
uses only exact-functor composition and the canonical inverse-image coefficient square.
Source: Stacks Tags 03DA and 06YY
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicQuotientPullComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (k : ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk ((d.ideal.map
            (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) ⋙
          adicLisseConstantModules X (AdicCompletion d.ideal A) ≅
        constantAdicQuotientModules X d n ⋙
          pbcRestrict ((constantAdicFiniteCone X d).π.app (op n))) :
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))).mapDerivedCategory ⋙
        constantAdicFiniteRealization g d ≅
      constantAdicQuotientRealization g d n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection g d n) := by
  have := CompletedConstantReduction.constant_additive X (AdicCompletion d.ideal A)
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
  let R := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk ((d.ideal.map
      (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
  let F := constantAdicQuotientModules X d n
  let H := pbcRestrict ((constantAdicFiniteCone X d).π.app (op n))
  let P := adicTowerPullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
  let kD : R.mapDerivedCategory ⋙
      (adicLisseConstantModules X (AdicCompletion d.ideal A)).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ H.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso R _ ≪≫
      Functor.mapDerivedCategoryNatIso k ≪≫ (Functor.mapDerivedCategoryCompIso F H).symm
  let kp := proEtaleRingRestrictionDerivedPullback g
    (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage g).obj
      (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)))
    ((constantAdicFiniteCone X d).π.app (op n))
    (constantAdicFiniteProjection g d n) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight kD P ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F.mapDerivedCategory kp.symm ≪≫
      (Functor.associator _ _ _).symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] CompletedConstantReduction.constant_additive

private theorem constant_limits (X : AlgebraicGeometry.Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    PreservesFiniteLimits (adicLisseConstantModules X B) :=
  (constantAdicFinite_constant_exact X B).1

private theorem constant_colimits (X : AlgebraicGeometry.Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    PreservesFiniteColimits (adicLisseConstantModules X B) :=
  (constantAdicFinite_constant_exact X B).2

attribute [local instance] constant_limits constant_colimits
attribute [local irreducible] Functor.leftAdjoint
  ConstantScalarRealization.derivedExtension ConstantScalarRealization.moduleDerivedExtension
  ConstantScalarRealization.derivedAdjunction ConstantScalarRealization.moduleDerivedAdjunction
-- Completion evaluation identifies the actual power quotients.
private theorem quotient_eval {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    constantAdicQuotientMap I n (AdicCompletion.evalₐ I (n + 1) x) =
      Ideal.Quotient.mk _ x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have he : AdicCompletion.evalₐ I (n + 1)
      (x - algebraMap A (AdicCompletion I A) a) = 0 := by
    simpa only [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Algebra.algebraMap_self, RingHom.id_apply] using sub_eq_zero.mpr ha.symm
  have hm : x - algebraMap A (AdicCompletion I A) a ∈
      (I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1) := by
    rw [← Ideal.map_pow]
    change x - algebraMap A (AdicCompletion I A) a ∈
      ((I ^ (n + 1)).map (algebraMap A (AdicCompletion I A))).restrictScalars A
    rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI]
    change AdicCompletion.eval I A (n + 1) _ = 0
    rw [← AdicCompletion.factor_evalₐ_eq_eval I _ (by simp), he]
    exact map_zero _
  rw [← ha]
  change Ideal.Quotient.mk _ (algebraMap A (AdicCompletion I A) a) =
    Ideal.Quotient.mk _ x
  exact (Ideal.Quotient.eq.mpr hm).symm

-- Iterated mates exchange inverse-image and scalar adjunctions.
private theorem scalar_pull_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : F₁ ⊣ U₁) (a₄ : F₂ ⊣ U₂)
    (t : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso (mateEquiv a₄ a₃ t)] :
    IsIso ((mateEquiv a₁ a₂).symm t) := by
  have h := conjugateEquiv_symm_iso (a₁.comp a₄) (a₃.comp a₂)
    (mateEquiv a₄ a₃ t)
  have he := 
    (iterated_mateEquiv_conjugateEquiv_symm a₁ a₂ a₃ a₄ ((mateEquiv a₄ a₃) t))
  simp only [Equiv.symm_apply_apply] at he
  change ((mateEquiv a₁ a₂).symm t) =
    (conjugateEquiv (a₁.comp a₄) (a₃.comp a₂)).symm
      (mateEquiv a₄ a₃ t) at he
  rw [he]
  exact h

private def pasteSquare
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {R₀ : B ⥤ A} {R₁ : D ⥤ C} {R₂ : F ⥤ E}
    {U₀₁ : A ⥤ C} {U₁₂ : C ⥤ E} {U₀₂ : A ⥤ E}
    {V₀₁ : B ⥤ D} {V₁₂ : D ⥤ F} {V₀₂ : B ⥤ F}
    (k₀₁ : R₀ ⋙ U₀₁ ≅ V₀₁ ⋙ R₁) (k₁₂ : R₁ ⋙ U₁₂ ≅ V₁₂ ⋙ R₂)
    (cU : U₀₂ ≅ U₀₁ ⋙ U₁₂) (cV : V₀₂ ≅ V₀₁ ⋙ V₁₂) :
    R₀ ⋙ U₀₂ ≅ V₀₂ ⋙ R₂ :=
  Functor.isoWhiskerLeft R₀ cU ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight k₀₁ U₁₂ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft V₀₁ k₁₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight cV.symm R₂

private theorem pasteSquare_fac
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {R₀ : B ⥤ A} {R₁ : D ⥤ C} {R₂ : F ⥤ E}
    {U₀₁ : A ⥤ C} {U₁₂ : C ⥤ E} {U₀₂ : A ⥤ E}
    {V₀₁ : B ⥤ D} {V₁₂ : D ⥤ F} {V₀₂ : B ⥤ F}
    (k₀₁ : R₀ ⋙ U₀₁ ≅ V₀₁ ⋙ R₁) (k₁₂ : R₁ ⋙ U₁₂ ≅ V₁₂ ⋙ R₂)
    (cU : U₀₂ ≅ U₀₁ ⋙ U₁₂) (cV : V₀₂ ≅ V₀₁ ⋙ V₁₂) (N : B) :
    (pasteSquare k₀₁ k₁₂ cU cV).hom.app N ≫ R₂.map (cV.hom.app N) =
      cU.hom.app (R₀.obj N) ≫ U₁₂.map (k₀₁.hom.app N) ≫ k₁₂.hom.app (V₀₁.obj N) := by
  simp only [pasteSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  rw [← R₂.map_comp, Iso.inv_hom_id_app, R₂.map_id]
  simp

private def tripleComparison
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {R₀ : B ⥤ A} {R₁ : C ⥤ A} {R₂ : D ⥤ E} {R₃ : F ⥤ E}
    {Q : B ⥤ C} {S : C ⥤ D} {V : D ⥤ F} {T : A ⥤ E}
    (k₁ : R₀ ⋙ 𝟭 A ≅ Q ⋙ R₁) (k₂ : R₁ ⋙ T ≅ S ⋙ R₂)
    (k₃ : R₂ ⋙ 𝟭 E ≅ V ⋙ R₃) : R₀ ⋙ T ≅ (Q ⋙ S ⋙ V) ⋙ R₃ :=
  pasteSquare (pasteSquare k₁ k₂ (Functor.leftUnitor T).symm (Iso.refl (Q ⋙ S)))
    k₃ (Functor.rightUnitor T).symm (Functor.associator Q S V).symm

-- Keep this calculation abstract: none of the coefficient objects need to unfold.
private theorem tripleComparison_mate_isIso
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
    (R₀ : B ⥤ A) (R₁ : C ⥤ A) (R₂ : D ⥤ E) (R₃ : F ⥤ E)
    (Q : B ⥤ C) (S : C ⥤ D) (V : D ⥤ F) (T : A ⥤ E)
    [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
    [Q.Additive] [S.Additive] [V.Additive] [T.Additive]
    [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [Q.IsEquivalence] [V.IsEquivalence]
    {L₀ : DerivedCategory A ⥤ DerivedCategory B}
    {L₁ : DerivedCategory A ⥤ DerivedCategory C}
    {L₂ : DerivedCategory E ⥤ DerivedCategory D}
    {L₃ : DerivedCategory E ⥤ DerivedCategory F}
    (a₀ : L₀ ⊣ R₀.mapDerivedCategory) (a₁ : L₁ ⊣ R₁.mapDerivedCategory)
    (a₂ : L₂ ⊣ R₂.mapDerivedCategory) (a₃ : L₃ ⊣ R₃.mapDerivedCategory)
    (k₁ : R₀ ⋙ 𝟭 A ≅ Q ⋙ R₁) (k₂ : R₁ ⋙ T ≅ S ⋙ R₂)
    (k₃ : R₂ ⋙ 𝟭 E ≅ V ⋙ R₃)
    (h₂ : IsIso ((mateEquiv a₁ a₂).symm
      (Functor.mapDerivedCategorySquareIso k₂).hom)) :
    IsIso ((mateEquiv a₀ a₃).symm
      (Functor.mapDerivedCategorySquareIso (tripleComparison k₁ k₂ k₃)).hom) := by
  let k₁₂ := pasteSquare k₁ k₂ (Functor.leftUnitor T).symm (Iso.refl (Q ⋙ S))
  have h₁ : IsIso ((mateEquiv a₀ a₁).symm
      (Functor.mapDerivedCategorySquareIso k₁).hom) :=
    isIso_inverseMate_of_equivalences a₀ a₁ (Functor.mapDerivedCategorySquareIso k₁)
  have h₁₂ : IsIso ((mateEquiv a₀ a₂).symm
      (Functor.mapDerivedCategorySquareIso k₁₂).hom) :=
    derivedScalarMatePasting R₀ R₁ R₂ (𝟭 A) T T Q S (Q ⋙ S)
      a₀ a₁ a₂ k₁ k₂ k₁₂ (Functor.leftUnitor T).symm (Iso.refl _)
      (pasteSquare_fac _ _ _ _) h₁ h₂
  have h₃ : IsIso ((mateEquiv a₂ a₃).symm
      (Functor.mapDerivedCategorySquareIso k₃).hom) :=
    isIso_inverseMate_of_equivalences a₂ a₃ (Functor.mapDerivedCategorySquareIso k₃)
  exact derivedScalarMatePasting R₀ R₂ R₃ T (𝟭 E) T (Q ⋙ S) V (Q ⋙ S ⋙ V)
    a₀ a₂ a₃ k₁₂ k₃ (tripleComparison k₁ k₂ k₃)
    (Functor.rightUnitor T).symm (Functor.associator Q S V).symm
    (pasteSquare_fac _ _ _ _) h₁₂ h₃

-- Construct the section-normalized comparison from the three coefficient squares.
private def ordinaryComparison (X : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.mk
        ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) ⋙
        adicLisseConstantModules X (AdicCompletion d.ideal A) ≅
      constantAdicQuotientModules X d n ⋙
        pbcRestrict ((constantAdicFiniteCone X d).π.app (op n)) := by
  let C := AdicCompletion d.ideal A
  let q := constantAdicQuotientMap d.ideal n
  let r := (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom
  let a := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom r)
  let b := (pbcLevelConstantComparison X d n).inv
  let c := (constantAdicFiniteCone X d).π.app (op n)
  have hab : c ≫ b = a := by
    change (a ≫ (pbcLevelConstantComparison X d n).hom) ≫
      (pbcLevelConstantComparison X d n).inv = a
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hq : (Ideal.Quotient.mk
      ((d.ideal.map (algebraMap A C)) ^ (n + 1))) = q.comp r := by
    ext x
    exact (quotient_eval d.ideal d.finitelyGenerated n x).symm
  let R := ModuleCat.restrictScalars (Ideal.Quotient.mk
    ((d.ideal.map (algebraMap A C)) ^ (n + 1)))
  let k₁ := Functor.rightUnitor R ≪≫ ModuleCat.restrictScalarsComp' r q _ hq
  let k₂ := (ConstantScalarRealization.restrictionIso (ProEt.topology X) r).symm
  let k₃ := Functor.rightUnitor (pbcRestrict a) ≪≫ (pbcRestrictComp c b a hab).symm
  exact tripleComparison k₁ k₂ k₃

private theorem restrictComp_inv_section
    {X : AlgebraicGeometry.Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : pbcModules X T) (V : X.ProEtᵒᵖ) (x : M.val.obj V) :
    ((pbcRestrictComp a b c h).inv.app M).val.app V x = x := by
  have hh := (pbcRestrictComp_exists a b c h).exists.choose_spec M V x
  change ((pbcRestrictComp a b c h).hom.app M).val.app V x = x at hh
  have hid := congrArg (fun t ↦ t.val.app V x)
    ((pbcRestrictComp a b c h).hom_inv_id_app M)
  change ((pbcRestrictComp a b c h).inv.app M).val.app V
    (((pbcRestrictComp a b c h).hom.app M).val.app V x) = x at hid
  rw [hh] at hid
  exact hid

private theorem sheafHom_comp_apply
    {X : AlgebraicGeometry.Scheme.{u}}
    {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    {M N P : SheafOfModules.{u + 1} R} (f : M ⟶ N) (g : N ⟶ P)
    (V : X.ProEtᵒᵖ) (x : M.val.obj V) :
    ((f ≫ g).val.app V) x = g.val.app V (f.val.app V x) := rfl

private theorem ordinaryComparison_sections (X : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (N : ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
    (V : X.ProEtᵒᵖ) (x : N) :
    ((ordinaryComparison X d n).hom.app N).val.app V
      (constantAdicModuleSection X (AdicCompletion d.ideal A)
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk
          ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))).obj N) V x) =
      constantAdicModuleSection X (A ⧸ d.ideal ^ (n + 1))
        ((ModuleCat.restrictScalars (constantAdicQuotientMap d.ideal n)).obj N) V x := by
  simp only [ordinaryComparison, tripleComparison, pasteSquare, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app, Iso.refl_inv,
    CategoryTheory.Functor.map_id, Functor.id_map, Functor.comp_obj, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  simp only [sheafHom_comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app]
  erw [restrictComp_inv_section]
  let q := constantAdicQuotientMap d.ideal n
  let r := (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom
  have hq : Ideal.Quotient.mk
      ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)) = q.comp r := by
    ext z
    exact (quotient_eval d.ideal d.finitelyGenerated n z).symm
  let f := (ModuleCat.restrictScalarsComp' r q _ hq).hom.app N
  have hn := ConstantScalarRealization.constantSection_naturality (ProEt.topology X) f V x
  exact (congrArg (fun z ↦
      ((ConstantScalarRealization.restrictionIso (ProEt.topology X) r).inv.app
        ((ModuleCat.restrictScalars q).obj N)).val.app V z) hn).trans
    (ConstantScalarRealization.restrictionIso_inv_constantSection (ProEt.topology X) r
      ((ModuleCat.restrictScalars q).obj N) V x)

private theorem eval_zero_of_mem {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) (x : AdicCompletion I A)
    (hx : x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1)) :
    AdicCompletion.evalₐ I (n + 1) x = 0 := by
  rw [← Ideal.map_pow] at hx
  change x ∈ ((I ^ (n + 1)).map
    (algebraMap A (AdicCompletion I A))).restrictScalars A at hx
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI] at hx
  change AdicCompletion.eval I A (n + 1) x = 0 at hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), hx]
  exact map_zero _

private theorem quotient_map_bijective {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    Function.Bijective (constantAdicQuotientMap I n) := by
  constructor
  · apply (injective_iff_map_eq_zero (constantAdicQuotientMap I n)).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (algebraMap A (AdicCompletion I A) a) = 0 at hx
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have he := eval_zero_of_mem I hI n _ hm
    simpa only [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Algebra.algebraMap_self, RingHom.id_apply] using he
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨AdicCompletion.evalₐ I (n + 1) x, quotient_eval I hI n x⟩

-- The other mate is the canonical invertible direct-image comparison.
private theorem inverseImage_mate_isIso {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    let b := (adicTowerInverseImage g).map a
    let k := proEtaleRingRestrictionDerivedPullback g R S
      ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
      a b (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    IsIso ((mateEquiv (pbcDerivedScalarAdjunction a)
      (pbcDerivedScalarAdjunction b)).symm k.inv) := by
  dsimp only
  let b := (adicTowerInverseImage g).map a
  let h := (Category.id_comp b).trans (Category.comp_id b).symm
  let k := proEtaleRingRestrictionDerivedPullback g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    a b (Iso.refl _) (Iso.refl _) h
  let ac := proEtaleRingDerivedAdjunction g R ((adicTowerInverseImage g).obj R) (Iso.refl _)
  let ad := proEtaleRingDerivedAdjunction g S ((adicTowerInverseImage g).obj S) (Iso.refl _)
  let t := TwoSquare.mk _ _ _ _ k.inv
  have he : (mateEquiv ad ac t) =
      (proEtaleRingRestrictionDerivedDirectImage g R S
        ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
        a b (Iso.refl _) (Iso.refl _) h).hom := by
    ext N
    have hh := (proEtaleRingSheafChangeAdjunction g R S
      ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
      a b (Iso.refl _) (Iso.refl _) h).2.2
        ((proEtaleRingDerivedDirectImage g S ((adicTowerInverseImage g).obj S)
          (Iso.refl _)).obj N) N (ad.counit.app N)
    have hc : ad.homEquiv _ _ (ad.counit.app N) = 𝟙 _ := by
      rw [← ad.homEquiv_symm_id N]
      exact Equiv.apply_symm_apply _ _
    dsimp only [ad] at hc
    erw [hc, CategoryTheory.Functor.map_id, Category.id_comp] at hh
    simpa [t, k, ac, ad, TwoSquare.mk,
      Adjunction.homEquiv_unit, mateEquiv_apply, Functor.comp_map, Category.assoc] using hh
  have : IsIso (mateEquiv ad ac t) := by rw [he]; infer_instance
  exact scalar_pull_mate (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    ac ad t

private theorem inverseMate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (s : TwoSquare R₁ G F R₂) (X : A) :
    ((mateEquiv a₁ a₂).symm s).app X =
      (a₂.homEquiv _ _).symm (F.map (a₁.unit.app X) ≫ s.app (L₁.obj X)) := by
  apply (a₂.homEquiv (F.obj X) (G.obj (L₁.obj X))).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a₁ a₂ s X).symm

private theorem constant_square_mate_isIso (X : AlgebraicGeometry.Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (r : R →+* S) :
    IsIso ((mateEquiv (ConstantScalarRealization.moduleDerivedAdjunction r)
      (ConstantScalarRealization.derivedAdjunction (ProEt.topology X) r)).symm
      (Functor.mapDerivedCategorySquareIso
        (ConstantScalarRealization.restrictionIso (ProEt.topology X) r).symm).hom) := by
  have ht : ((mateEquiv (ConstantScalarRealization.moduleDerivedAdjunction r)
      (ConstantScalarRealization.derivedAdjunction (ProEt.topology X) r)).symm
      (Functor.mapDerivedCategorySquareIso
        (ConstantScalarRealization.restrictionIso (ProEt.topology X) r).symm).hom) =
      ConstantScalarRealization.comparisonTransformation (ProEt.topology X) r := by
    apply NatTrans.ext
    funext M
    erw [inverseMate_app (ConstantScalarRealization.moduleDerivedAdjunction r)
      (ConstantScalarRealization.derivedAdjunction (ProEt.topology X) r)
      (Functor.mapDerivedCategorySquareIso
        (ConstantScalarRealization.restrictionIso (ProEt.topology X) r).symm).hom M]
    simp only [Functor.square_symm_hom]
    rfl
  rw [ht]
  exact (ConstantScalarRealization.constantRealizationDerivedScalarExtension
    (ProEt.topology X) r).1

-- Instantiate the abstract calculation without unfolding chosen adjoints.
private theorem ordinaryComparison_mate_isIso (X : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (L : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (adj : L ⊣ (ModuleCat.restrictScalars (Ideal.Quotient.mk
      ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))).mapDerivedCategory) :
    IsIso ((mateEquiv adj
      (pbcDerivedScalarAdjunction ((constantAdicFiniteCone X d).π.app (op n)))).symm
      (Functor.mapDerivedCategorySquareIso (ordinaryComparison X d n)).hom) := by
  let C := AdicCompletion d.ideal A
  let q := constantAdicQuotientMap d.ideal n
  let r := (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom
  let a := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom r)
  let b := (pbcLevelConstantComparison X d n).inv
  let c := (constantAdicFiniteCone X d).π.app (op n)
  have hab : c ≫ b = a := by
    change (a ≫ (pbcLevelConstantComparison X d n).hom) ≫
      (pbcLevelConstantComparison X d n).inv = a
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hq : (Ideal.Quotient.mk
      ((d.ideal.map (algebraMap A C)) ^ (n + 1))) = q.comp r := by
    ext x
    exact (quotient_eval d.ideal d.finitelyGenerated n x).symm
  let Q := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q
  let S := adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1))
  let T := adicLisseConstantModules X C
  have : T.Additive := CompletedConstantReduction.constant_additive X C
  have : PreservesFiniteLimits T := (constantAdicFinite_constant_exact X C).1
  have : PreservesFiniteColimits T := (constantAdicFinite_constant_exact X C).2
  have : S.Additive := CompletedConstantReduction.constant_additive X _
  have : PreservesFiniteLimits S := (constantAdicFinite_constant_exact X _).1
  have : PreservesFiniteColimits S := (constantAdicFinite_constant_exact X _).2
  let R := ModuleCat.restrictScalars (Ideal.Quotient.mk
    ((d.ideal.map (algebraMap A C)) ^ (n + 1)))
  let k₁ := Functor.rightUnitor R ≪≫ ModuleCat.restrictScalarsComp' r q _ hq
  let k₂ := (ConstantScalarRealization.restrictionIso (ProEt.topology X) r).symm
  let k₃ := Functor.rightUnitor (pbcRestrict a) ≪≫ (pbcRestrictComp c b a hab).symm
  let a₁ := ConstantScalarRealization.moduleDerivedAdjunction r
  let a₂ := ConstantScalarRealization.derivedAdjunction (ProEt.topology X) r
  let a₃ := pbcDerivedScalarAdjunction c
  let eqv := RingEquiv.ofBijective q (quotient_map_bijective d.ideal d.finitelyGenerated n)
  have : Q.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars eqv.toRingHom).IsEquivalence
  have : (pbcRestrict b).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X
      ((adicLisseForget X).mapIso (pbcLevelConstantComparison X d n).symm)).functor.IsEquivalence
  exact tripleComparison_mate_isIso R (ModuleCat.restrictScalars r) (pbcRestrict a)
    (pbcRestrict c) Q S (pbcRestrict b) T adj a₁ a₂ a₃ k₁ k₂ k₃
    (constant_square_mate_isIso X r)

private theorem pullComparison_mate_isIso {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (L : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (adj : L ⊣ (ModuleCat.restrictScalars (Ideal.Quotient.mk
      ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))).mapDerivedCategory) :
    IsIso ((mateEquiv adj
      (pbcDerivedScalarAdjunction (constantAdicFiniteProjection g d n))).symm
      (constantAdicQuotientPullComparison g d n (ordinaryComparison X d n)).hom) := by
  have := CompletedConstantReduction.constant_additive X (AdicCompletion d.ideal A)
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
  let c := (constantAdicFiniteCone X d).π.app (op n)
  let kD := Functor.mapDerivedCategorySquareIso (ordinaryComparison X d n)
  let kp := proEtaleRingRestrictionDerivedPullback g
    (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage g).obj
      (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)))
    c (constantAdicFiniteProjection g d n) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  have h₁ := ordinaryComparison_mate_isIso X d n L adj
  have h₂ := inverseImage_mate_isIso g c
  refine CategoryTheory.mate_paste_isIso adj (pbcDerivedScalarAdjunction c)
    (pbcDerivedScalarAdjunction (constantAdicFiniteProjection g d n))
    kD kp.symm (constantAdicQuotientPullComparison g d n (ordinaryComparison X d n))
    (Iso.refl (constantAdicFiniteRealization g d))
    (Iso.refl (constantAdicQuotientRealization g d n)) ?_ h₁ h₂
  ext M
  simp only [Functor.const_obj_obj, Functor.comp_obj, Iso.refl_hom,
    Functor.whiskerLeft_id', Iso.symm_hom, Iso.refl_inv, Category.id_comp,
    NatTrans.comp_app, TwoSquare.vComp_app, Functor.whiskerRight_app,
    NatTrans.id_app, Category.assoc]
  let : Category.{u + 2} (DerivedCategory
      (pbcModules Y ((adicTowerInverseImage g).obj (constantAdicFiniteCone X d).pt))) :=
    inferInstanceAs (Category.{u + 2} (DerivedCategory
      (pbcModules Y ((adicTowerInverseImage g).obj
        (adicLisseConstantRing X (AdicCompletion d.ideal A))))))
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  let P := adicTowerPullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
  let f := P.map (kD.hom.app M)
  let t := kp.inv.app ((constantAdicQuotientModules X d n).mapDerivedCategory.obj M)
  change (𝟙 _ ≫ f ≫ 𝟙 _ ≫ t ≫ 𝟙 _) = f ≫ t
  simp only [Category.id_comp, Category.comp_id]

/-- The unique identity-on-constant-sections coefficient comparison has invertible
left mate for arbitrary algebraic derived objects and arbitrary scalar left adjoints.
There is no tower, local-system, or boundedness assumption in this assertion.

Source: Stacks Tags 093J, 031C, 03DA and 06YY.
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison).

Proof: completion evaluation and the power-kernel formula identify the actual
quotient map as an isomorphism. Paste module restriction composition, the proved
constant-realization restriction comparison, and finite-coefficient transport.
These maps preserve constant sections, which determine morphisms from constant
modules, proving uniqueness. The inverse scalar mates of the first and last
squares are invertible because their transverse functors are equivalences; the
middle square uses the general unbounded constant-realization scalar theorem.
Exact localization respects this pasting. For the inverse-image square, the
ring-sheaf-change adjunct identity identifies its other mate with the invertible
direct-image comparison. Iterated mates then give invertibility of its scalar
mate. Paste once more and use the mate unit equation to obtain the displayed
component for the arbitrary supplied adjunction. No nontriviality or geometric
finiteness hypothesis is used. -/
theorem constantAdicQuotientScalarComparison (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    let C := AdicCompletion d.ideal A
    let J := d.ideal.map (algebraMap A C)
    let R := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (Ideal.Quotient.mk (J ^ (n + 1)))
    ∃! k : R ⋙ adicLisseConstantModules X C ≅
        constantAdicQuotientModules X d n ⋙
          pbcRestrict ((constantAdicFiniteCone X d).π.app (op n)),
      (∀ (N : ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))) (V : X.ProEtᵒᵖ) (x : N),
        (k.hom.app N).val.app V (constantAdicModuleSection X C (R.obj N) V x) =
          constantAdicModuleSection X (A ⧸ d.ideal ^ (n + 1))
            ((ModuleCat.restrictScalars (constantAdicQuotientMap d.ideal n)).obj N) V x) ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ X)
        (E : DerivedCategory (ModuleCat.{u + 1} C))
        (L : DerivedCategory (ModuleCat.{u + 1} C) ⥤
          DerivedCategory (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))))
        (adj : L ⊣ R.mapDerivedCategory),
        IsIso (((pbcDerivedScalarAdjunction (constantAdicFiniteProjection g d n)).homEquiv
          ((constantAdicFiniteRealization g d).obj E)
          ((constantAdicQuotientRealization g d n).obj (L.obj E))).symm
            ((constantAdicFiniteRealization g d).map (adj.unit.app E) ≫
              (constantAdicQuotientPullComparison g d n k).hom.app (L.obj E))) := by
  refine ⟨ordinaryComparison X d n, ⟨ordinaryComparison_sections X d n, ?_⟩, ?_⟩
  · intro Y g E L adj
    have := pullComparison_mate_isIso g d n L adj
    erw [← inverseMate_app adj
      (pbcDerivedScalarAdjunction (constantAdicFiniteProjection g d n))
      (constantAdicQuotientPullComparison g d n (ordinaryComparison X d n)).hom E]
    infer_instance
  · intro k hk
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply ConstantScalarRealization.constantSection_ext (ProEt.topology X)
    intro V x
    exact (hk.1 N V x).trans (ordinaryComparison_sections X d n N V x).symm

/-- The section-normalized ordinary comparison, determined uniquely by the preceding
theorem; no choice of an unspecified object is involved.
Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicQuotientComparison (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  (constantAdicQuotientScalarComparison X d n).exists.choose

/-- The canonical derived right square for constants and finite restriction.
Source: Stacks Tag 06YY
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison). -/
def constantAdicQuotientRightIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  constantAdicQuotientPullComparison g d n (constantAdicQuotientComparison X d n)

end AlgebraicGeometry.Scheme
