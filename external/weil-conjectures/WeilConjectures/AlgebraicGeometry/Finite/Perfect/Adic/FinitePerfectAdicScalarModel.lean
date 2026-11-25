/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarModelFactors
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The constant-model comparison for explicit scalar realization

Source: Stacks Project, Tags 093J, 093M, 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem deriveOrdinarySquare
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (R : C ⥤ D) (F₀ G₀ : C ⥤ E) (F₁ G₁ : D ⥤ E)
    [R.Additive] [F₀.Additive] [G₀.Additive] [F₁.Additive] [G₁.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    (s : R ⋙ F₁ ≅ F₀) (z : R ⋙ G₁ ≅ G₀)
    (e₀ : F₀ ≅ G₀) (e₁ : F₁ ≅ G₁)
    (h : ∀ N, e₁.hom.app (R.obj N) ≫ z.hom.app N =
      s.hom.app N ≫ e₀.hom.app N) :
    whiskerLeft R.mapDerivedCategory (mapDerivedCategoryNatIso e₁).hom ≫
        (mapDerivedCategoryCompIso R G₁).hom ≫
        (mapDerivedCategoryNatIso z).hom =
      (mapDerivedCategoryCompIso R F₁).hom ≫
        (mapDerivedCategoryNatIso s).hom ≫ (mapDerivedCategoryNatIso e₀).hom := by
  have he : isoWhiskerLeft R e₁ ≪≫ z = s ≪≫ e₀ := by
    apply Iso.ext
    exact NatTrans.ext (funext h)
  have hd := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom) he
  simp only [mapDerivedCategoryNatIso_trans] at hd
  have hw := mapDerivedCategoryNatIso_isoWhiskerLeft R e₁
  apply (cancel_epi (mapDerivedCategoryCompIso R F₁).inv).mp
  calc
    _ = (mapDerivedCategoryNatIso (isoWhiskerLeft R e₁)).hom ≫
        (mapDerivedCategoryNatIso z).hom := by
      rw [← Category.assoc, ← hw]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (mapDerivedCategoryNatIso s).hom ≫ (mapDerivedCategoryNatIso e₀).hom := hd
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

private theorem deriveTargetStep
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (R : C ⥤ D) (S : D ⥤ E) (T : C ⥤ E) (H : E ⥤ F)
    [R.Additive] [S.Additive] [T.Additive] [H.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : T ≅ R ⋙ S) (J : DerivedCategory E ⥤ DerivedCategory F)
    (g : H.mapDerivedCategory ≅ J) :
    let k₀ := (mapDerivedCategoryCompIso T H).symm ≪≫ isoWhiskerLeft T.mapDerivedCategory g
    let k₁ := (mapDerivedCategoryCompIso S H).symm ≪≫ isoWhiskerLeft S.mapDerivedCategory g
    (mapDerivedCategoryCompIso R (S ⋙ H)).hom ≫
        (mapDerivedCategoryNatIso (isoWhiskerRight c.symm H)).hom ≫ k₀.hom =
      whiskerLeft R.mapDerivedCategory k₁.hom ≫
        whiskerRight (mapDerivedCategoryNatIso c ≪≫
          (mapDerivedCategoryCompIso R S).symm).inv J := by
  dsimp only
  have hw := mapDerivedCategoryNatIso_isoWhiskerRight c.symm H
  rw [mapDerivedCategoryNatIso_symm] at hw
  have ha := mapDerivedCategoryCompIso_assoc R S H
  have hr : (mapDerivedCategoryCompIso R (S ⋙ H)).hom ≫
      (mapDerivedCategoryCompIso (R ⋙ S) H).inv =
    whiskerLeft R.mapDerivedCategory (mapDerivedCategoryCompIso S H).inv ≫
      whiskerRight (mapDerivedCategoryCompIso R S).hom H.mapDerivedCategory := by
    apply NatTrans.ext
    funext K
    have hk := NatTrans.congr_app ha K
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hk ⊢
    apply (cancel_epi
      ((mapDerivedCategoryCompIso R (S ⋙ H)).inv.app K)).mp
    apply (cancel_mono
      (H.mapDerivedCategory.map ((mapDerivedCategoryCompIso R S).inv.app K))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    simp only [H.mapDerivedCategory.map_id]
    simp only [Functor.comp_obj] at hk ⊢
    rw [Category.comp_id]
    exact hk.symm
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, isoWhiskerLeft_hom]
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  have hwK := NatTrans.congr_app hw K
  have hrK := NatTrans.congr_app hr K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hwK hrK
  simp only [Category.assoc]
  rw [reassoc_of% hwK, reassoc_of% hrK]
  simpa only [Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ (mapDerivedCategoryCompIso S H).inv.app
    (R.mapDerivedCategory.obj K) ≫ z)
    (g.hom.naturality ((mapDerivedCategoryCompIso R S).hom.app K ≫
      (mapDerivedCategoryNatIso c).inv.app K))

namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Constant algebraic quotient complexes have the canonical realized model diagram,
including its specified consecutive arrows.

Source: Stacks Project, Tags 093J, 093M, 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-model).

Proof: represent each perfect level by a bounded complex of finite projective modules.
Universe lift and exact constant realization preserve these representatives and their
finite-projective splittings. Inverse image to U, restriction along W and transport to
the slice commute with constants, by their constant-section units. The locally bijective
finite coefficient unit identifies the resulting fixed-ring module sheaf with the
actual quotient-ring module sheaf. After forgetting quotient scalars, flatness of the
completed constant ring over the constant A-ring and its canonical finite reduction
identify this with completed scalar extension of the A-restriction of the algebraic
level. These natural identifications give model. On an algebraic quotient arrow all
comparisons send a constant pure tensor to that same constant section. Associativity
of scalar restriction and the equation between the two consecutive completed
projections show that the two displayed composites agree on these generators.
Sheafification, termwise total complexes and localization preserve this equality,
giving the specified model_normalized equation. This does not select a marking or
use an actual quotient of M. Zero rings, zero complexes and empty charts use the same
canonical tensor and sheafification maps. -/
theorem finitePerfectAdicScalar_model
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n)) :
    ∃ model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n),
      ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition V.left T n)) ≫
      (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op  := by
  classical
  have _ := hperfect
  choose e he using fun (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) ↦
      finitePerfectAdicOrdinaryScalar_model X d V U W f
  let m (U : V.left.ProEt) (W : X.ProEt)
      (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :=
    (finitePerfectAdicScalarModelSourceFactors X d V U W f n).symm ≪≫
      mapDerivedCategoryNatIso (e U W f n) ≪≫
        finitePerfectAdicScalarModelTargetFactors X d W n
  have square (U : V.left.ProEt) (W : X.ProEt)
      (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
      (K : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))) :
      (m U W f (n + 1)).hom.app
          ((DerivedCategory.adicStepRestriction d.ideal n).obj K) ≫
        (finitePerfectAdicLocalRealization X d W).map
          ((DerivedCategory.adicRestrictionComp d.ideal n).inv.app K) =
      (finitePerfectAdicScalarModelSourceStep X d V U W f n).hom.app K ≫
        (m U W f n).hom.app K := by
    let R := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    let S := ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)))
    let T₀ := ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    let H := finitePerfectAdicScalarModelOrdinary X d ⋙
      SheafOfModules.overFunctor (completedAdicRing X d) W
    let J := finitePerfectAdicLocalRealization X d W
    let c := ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm
    have := (finitePerfectAdicConstant_exact X A).1
    have := (finitePerfectAdicConstant_exact X A).2.1
    have := (finitePerfectAdicConstant_exact X A).2.2
    have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).1
    have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.1
    have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.2
    let g : H.mapDerivedCategory ≅ J :=
      (mapDerivedCategoryCompIso (finitePerfectAdicScalarModelOrdinary X d)
        (SheafOfModules.overFunctor (completedAdicRing X d) W)).symm ≪≫
      isoWhiskerRight (finitePerfectAdicScalarModelCompletedFactors X d)
        (ringedDerivedRestrictionGeneral (completedAdicRing X d) W)
    have hd := deriveOrdinarySquare R
      (finitePerfectAdicOrdinaryScalarSource X d V U W f n)
      (finitePerfectAdicOrdinaryScalarTarget X d W n)
      (finitePerfectAdicOrdinaryScalarSource X d V U W f (n + 1))
      (finitePerfectAdicOrdinaryScalarTarget X d W (n + 1))
      (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n)
      (finitePerfectAdicOrdinaryScalarTargetStep X d W n)
      (e U W f n) (e U W f (n + 1)) (he U W f n)
    have hsrc := finitePerfectAdicScalarModelSource_localization X d V U W f n
    dsimp only at hsrc
    have hs := congrArg (fun z ↦
      (mapDerivedCategoryCompIso R
        (finitePerfectAdicOrdinaryScalarSource X d V U W f (n + 1))).hom ≫ z)
      hsrc
    simp only [R, Iso.hom_inv_id_assoc] at hs
    have ht := deriveTargetStep R S T₀ H c J g
    have htK := NatTrans.congr_app ht K
    have hsK := NatTrans.congr_app hs K
    have hdK := NatTrans.congr_app hd K
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hsK hdK htK
    change (mapDerivedCategoryCompIso R
        (finitePerfectAdicOrdinaryScalarTarget X d W (n + 1))).hom.app K ≫
      (mapDerivedCategoryNatIso
        (finitePerfectAdicOrdinaryScalarTargetStep X d W n)).hom.app K ≫
      (finitePerfectAdicScalarModelTargetFactors X d W n).hom.app K =
      (finitePerfectAdicScalarModelTargetFactors X d W (n + 1)).hom.app
        (R.mapDerivedCategory.obj K) ≫ J.map
          ((DerivedCategory.adicRestrictionComp d.ideal n).inv.app K) at htK
    change (m U W f (n + 1)).hom.app (R.mapDerivedCategory.obj K) ≫ J.map
        ((DerivedCategory.adicRestrictionComp d.ideal n).inv.app K) =
      (finitePerfectAdicScalarModelSourceStep X d V U W f n).hom.app K ≫
        (m U W f n).hom.app K
    apply (cancel_epi ((finitePerfectAdicScalarModelSourceFactors
      X d V U W f (n + 1)).hom.app (R.mapDerivedCategory.obj K))).mp
    dsimp only [m, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hsK]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hdK]
    rw [htK]
  refine ⟨fun U W f n ↦ (m U W f n).app (T.level n), ?_⟩
  intro U W f n
  have hs :
      (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
          (localProEtaleNormalization U.hom
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
            (finitePerfectAdicEtaleConstantTransition V.left T n)) ≫
        (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
          ((localProEtaleComparison U.hom
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
            (finitePerfectAdicEtaleConstant V.left T n)) =
      (finitePerfectAdicScalarModelSource X d V U W f (n + 1)).map (T.transition n) ≫
        (finitePerfectAdicScalarModelSourceStep X d V U W f n).hom.app (T.level n) := by
    simp only [finitePerfectAdicScalarModelSource, finitePerfectAdicScalarModelSourceStep,
      finitePerfectAdicPasteCoefficientStep,
      finitePerfectAdicEtaleConstantTransition, finitePerfectAdicEtaleConstant,
      finitePerfectAdicLiftedTransition, localProEtaleNormalization,
      normalizationConstantArrow, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
      Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc]
  dsimp only [Iso.app_hom]
  rw [← Category.assoc, hs, Category.assoc, ← square U W f n (T.level n)]
  rw [← Category.assoc, (m U W f (n + 1)).hom.naturality]
  simp only [finitePerfectAdicModelDiagram, Functor.comp_map,
    Functor.ofOpSequence_map_homOfLE_succ, DerivedCategory.adicTowerTransition,
    Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme
