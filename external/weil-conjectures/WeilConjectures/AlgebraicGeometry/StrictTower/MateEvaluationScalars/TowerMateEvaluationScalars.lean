/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport

/-! # Evaluation and scalar restriction of the clopen proper/open mate

Source: Stacks Project, sites-cohomology.tex, Tags 07A7 and 0D6E;
sites-modules.tex, Tags 03DI and 03DJ, and the strict-tower refinement
(blueprint: lem-cbc-tower-mate-evaluation-scalars).

The single-level arrow is the exact descent of the existing ordinary clopen arrow.
All comparison maps are constructed from the specified adjunctions. Index `n` means
positive level `n+1`; no boundedness, flatness or finite-coefficient assumption occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars

section ExactTransformations
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D H : Type*} [Category C] [Category D] [Category H]
  [Abelian C] [Abelian D] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
  {F G : C ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private def exactNat (t : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q)

@[reassoc] private theorem exactNat_fac (t : F ⟶ G) (K : CochainComplex C ℤ) :
    (exactNat t).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory =
      F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) G.mapDerivedCategory =
      G.mapDerivedCategoryFactors := rfl
  simp only [exactNat, Localization.liftNatTrans_app, hF, hG, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Functor.whiskerRight_app]

private theorem exactNat_comp (t : F ⟶ G) {J : C ⥤ D}
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J] (s : G ⟶ J) :
    exactNat (t ≫ s) = exactNat t ≫ exactNat s := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (J.mapDerivedCategoryFactors.hom.app K)).1
  simp only [NatTrans.comp_app, Category.assoc, exactNat_fac,
    exactNat_fac_assoc, NatTrans.mapHomologicalComplex_comp, Functor.map_comp]

private theorem exactNat_iso (e : F ≅ G) :
    exactNat e.hom = (Functor.mapDerivedCategoryNatIso e).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app K)).1
  rw [exactNat_fac, Functor.mapDerivedCategoryNatIso_fac]

private theorem exactNat_whiskerRight (t : F ⟶ G) (K : D ⥤ H)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K] :
    exactNat (Functor.whiskerRight t K) ≫ (Functor.mapDerivedCategoryCompIso G K).inv =
      (Functor.mapDerivedCategoryCompIso F K).inv ≫
        Functor.whiskerRight (exactNat t) K.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (fun L ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (K.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app L) ≫
      K.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj L)),
    Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors, exactNat_fac,
    Category.assoc, ← Functor.map_comp_assoc, exactNat_fac, Functor.map_comp_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

private theorem exactNat_whiskerLeft (K : H ⥤ C)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K] (t : F ⟶ G) :
    exactNat (Functor.whiskerLeft K t) ≫ (Functor.mapDerivedCategoryCompIso K G).inv =
      (Functor.mapDerivedCategoryCompIso K F).inv ≫
        Functor.whiskerLeft K.mapDerivedCategory (exactNat t) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso H (.up ℤ)) (fun L ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (K.mapDerivedCategoryFactors.hom.app L) ≫
      G.mapDerivedCategoryFactors.hom.app ((K.mapHomologicalComplex (.up ℤ)).obj L)),
    Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors, exactNat_fac,
    Category.assoc, ← reassoc_of% ((exactNat t).naturality
      (K.mapDerivedCategoryFactors.hom.app L)), exactNat_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

private theorem exactNat_square
    {C' D' : Type*} [Category C'] [Category D'] [Abelian C'] [Abelian D']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    {F' G' : C' ⥤ D'}
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (u : C ⥤ C') (v : D ⥤ D')
    [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (p : F ⋙ v ≅ u ⋙ F') (q : G ⋙ v ≅ u ⋙ G') (t : F ⟶ G) (t' : F' ⟶ G')
    (h : Functor.whiskerRight t v ≫ q.hom = p.hom ≫ Functor.whiskerLeft u t') :
    Functor.whiskerRight (exactNat t) v.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso q).hom =
      (Functor.mapDerivedCategorySquareIso p).hom ≫
        Functor.whiskerLeft u.mapDerivedCategory (exactNat t') := by
  have hm : exactNat (Functor.whiskerRight t v) ≫
      (Functor.mapDerivedCategoryNatIso q).hom =
      (Functor.mapDerivedCategoryNatIso p).hom ≫
        exactNat (Functor.whiskerLeft u t') := by
    rw [← exactNat_iso, ← exactNat_iso, ← exactNat_comp, ← exactNat_comp, h]
  have hR := exactNat_whiskerRight t v
  have hL := exactNat_whiskerLeft u t'
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso F v).inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hR, Iso.inv_hom_id_assoc, reassoc_of% hm, hL]

private theorem exactNat_unique (t : F ⟶ G) (δ : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (h : ClopenProjectorDescent F G t δ) : δ = exactNat t := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app K)).1
  rw [exactNat_fac]
  exact h K

variable [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]

private theorem evalD_trans (t : F ⟶ G) (n : ℕ) :
    Functor.whiskerRight
        (exactNat ((Functor.whiskeringRight ℕᵒᵖ C D).map t))
        (E D n).mapDerivedCategory ≫ (evalD G n).hom =
      (evalD F n).hom ≫ Functor.whiskerLeft (E C n).mapDerivedCategory
        (exactNat t) := by
  have h₁ := exactNat_whiskerRight
    ((Functor.whiskeringRight ℕᵒᵖ C D).map t) (E D n)
  have h₂ := exactNat_whiskerLeft (E C n) t
  have he : Functor.whiskerRight ((Functor.whiskeringRight ℕᵒᵖ C D).map t) (E D n) =
      Functor.whiskerLeft (E C n) t := rfl
  rw [he] at h₁
  dsimp only [evalD, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (W F) (E D n)).inv]
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, Iso.inv_hom_id_assoc]
  rw [Iso.inv_hom_id_assoc]
  exact h₂

private def exactSquare
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F₁ F₂).hom ≫ exactNat t ≫
    (Functor.mapDerivedCategoryCompIso G₁ G₂).inv

private theorem evalD_square_trans
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ A')]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) (M : DerivedCategory (ℕᵒᵖ ⥤ C)) (n : ℕ) :
    (E D n).mapDerivedCategory.map
        ((exactSquare (W F₁) (W F₂) (W G₁) (W G₂)
          (Functor.termwiseCompositeTransformation ℕᵒᵖ C A A' D F₁ F₂ G₁ G₂ t)).app M) ≫
      (evalD G₂ n).hom.app ((W G₁).mapDerivedCategory.obj M) ≫
      G₂.mapDerivedCategory.map ((evalD G₁ n).hom.app M) =
    (evalD F₂ n).hom.app ((W F₁).mapDerivedCategory.obj M) ≫
      F₂.mapDerivedCategory.map ((evalD F₁ n).hom.app M) ≫
      (exactSquare F₁ F₂ G₁ G₂ t).app ((E C n).mapDerivedCategory.obj M) := by
  have ht : Functor.termwiseCompositeTransformation ℕᵒᵖ C A A' D F₁ F₂ G₁ G₂ t =
      (Functor.whiskeringRight ℕᵒᵖ C D).map t := by
    ext L m
    simp [Functor.termwiseCompositeTransformation, Functor.whiskeringRightObjCompIso]
  rw [ht]
  have hF := congrArg (fun z ↦ z.app M) (evalD_comp F₁ F₂ n)
  have hG := congrArg (fun z ↦ z.app M) (evalD_comp G₁ G₂ n)
  have he := congrArg (fun z ↦ z.app M) (evalD_trans t n)
  dsimp only [exactSquare, NatTrans.comp_app] at *
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app] at hF hG he
  rw [← cancel_epi ((E D n).mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso (W F₁) (W F₂)).inv.app M))]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, hG, reassoc_of% he, reassoc_of% hF]
  simp only [Iso.inv_hom_id_app_assoc]

omit [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)] in
private theorem exactSquare_unique
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    (a : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory)
    (h : ClopenProjectorDescent (F₁ ⋙ F₂) (G₁ ⋙ G₂) t
      ((Functor.mapDerivedCategoryCompIso F₁ F₂).inv ≫ a ≫
        (Functor.mapDerivedCategoryCompIso G₁ G₂).hom)) :
    a = exactSquare F₁ F₂ G₁ G₂ t := by
  have he := exactNat_unique t _ h
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso F₁ F₂).inv,
    ← cancel_mono (Functor.mapDerivedCategoryCompIso G₁ G₂).hom]
  simpa only [exactSquare, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using he

end ExactTransformations

section ExactEvaluation
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
  {L : C ⥤ D} {R : D ⥤ C}
  [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

end ExactEvaluation

section ExactScalarDescent
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exactSquare_scalar
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    {F : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D}
    {F' : A' ⥤ B'} {G' : A' ⥤ C'} {H' : B' ⥤ D'} {K' : C' ⥤ D'}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [F'.Additive] [G'.Additive] [H'.Additive] [K'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (u₀ : A ⥤ A') (u₁ : B ⥤ B') (u₂ : C ⥤ C') (u₃ : D ⥤ D')
    [u₀.Additive] [u₁.Additive] [u₂.Additive] [u₃.Additive]
    [PreservesFiniteLimits u₀] [PreservesFiniteColimits u₀]
    [PreservesFiniteLimits u₁] [PreservesFiniteColimits u₁]
    [PreservesFiniteLimits u₂] [PreservesFiniteColimits u₂]
    [PreservesFiniteLimits u₃] [PreservesFiniteColimits u₃]
    (pF : F ⋙ u₁ ≅ u₀ ⋙ F') (pG : G ⋙ u₂ ≅ u₀ ⋙ G')
    (pH : H ⋙ u₃ ≅ u₁ ⋙ H') (pK : K ⋙ u₃ ≅ u₂ ⋙ K')
    (t : G ⋙ K ⟶ F ⋙ H) (t' : G' ⋙ K' ⟶ F' ⋙ H')
    (h : ∀ L, u₃.map (t.app L) ≫ pH.hom.app (F.obj L) ≫ H'.map (pF.hom.app L) =
      pK.hom.app (G.obj L) ≫ K'.map (pG.hom.app L) ≫ t'.app (u₀.obj L))
    (M : DerivedCategory A) :
    u₃.mapDerivedCategory.map ((exactSquare G K F H t).app M) ≫
        (Functor.mapDerivedCategorySquareIso pH).hom.app (F.mapDerivedCategory.obj M) ≫
        H'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso pF).hom.app M) =
      (Functor.mapDerivedCategorySquareIso pK).hom.app (G.mapDerivedCategory.obj M) ≫
        K'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso pG).hom.app M) ≫
        (exactSquare G' K' F' H' t').app (u₀.mapDerivedCategory.obj M) := by
  let a := Functor.associator G K u₃ ≪≫
    Functor.isoWhiskerLeft G pK ≪≫
    (Functor.associator G u₂ K').symm ≪≫
    Functor.isoWhiskerRight pG K' ≪≫
    Functor.associator u₀ G' K'
  let b := Functor.associator F H u₃ ≪≫
    Functor.isoWhiskerLeft F pH ≪≫
    (Functor.associator F u₁ H').symm ≪≫
    Functor.isoWhiskerRight pF H' ≪≫
    Functor.associator u₀ F' H'
  have hc : Functor.whiskerRight t u₃ ≫ b.hom =
      a.hom ≫ Functor.whiskerLeft u₀ t' := by
    apply NatTrans.ext
    funext L
    simpa only [a, b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
      using h L
  have hd := congrArg (fun z ↦ z.app M)
    (exactNat_square u₀ u₃ a b
      t t' hc)
  have ha := Functor.exactSquare_comp_forward G K
    (G ⋙ K) G' K'
    (G' ⋙ K') u₀ u₂
    u₃ pG pK a (Iso.refl _) (Iso.refl _)
    (by intro L; simp [a]) M
  have hb := Functor.exactSquare_comp_forward F H
    (F ⋙ H) F' H'
    (F' ⋙ H') u₀ u₁
    u₃ pF pH b (Iso.refl _) (Iso.refl _)
    (by intro L; simp [b]) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_refl,
    Category.id_comp] at ha hb
  rw [← cancel_epi (u₃.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso G K).inv.app M))]
  simp only [exactSquare, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.assoc, Iso.symm_hom] at ha hb
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hd
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hd ⊢
  rw [hb, reassoc_of% hd]
  have he := congrArg (fun z ↦ z ≫
    (Functor.mapDerivedCategoryCompIso G' K').hom.app
      (u₀.mapDerivedCategory.obj M) ≫
    (exactNat t').app (u₀.mapDerivedCategory.obj M) ≫
    (Functor.mapDerivedCategoryCompIso F' H').inv.app
      (u₀.mapDerivedCategory.obj M)) ha
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at he
  exact he.symm

end ExactScalarDescent

variable (B : Type (u + 1)) [CommRing B]

attribute [local instance] WeilConjectures.sfAbBijective

/-- The existing abelian structure with its coefficient universe made explicit.
Source: Stacks 03DA (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance modulesAbelian (X : Scheme.{u}) : Abelian (Modules B X) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

/-- The existing single-level exact inverse image, abbreviated for the formulas below.
Source: Stacks 03EK, 07A6 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev g {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules B Y) ⥤ DerivedCategory (Modules B X) :=
  (modulePullback B f).mapDerivedCategory

/-- The existing single-level total direct image.
Source: Stacks 07A5 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev r {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules B X) ⥤ DerivedCategory (Modules B Y) :=
  (moduleDirectImage B f).rightDerivedFunctor

/-- Exact descent of the existing single-level extension by zero.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev j {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    DerivedCategory (Modules B U) ⥤ DerivedCategory (Modules B X) :=
  (moduleJ B f).mapDerivedCategory

/-- The specified single-level derived adjunction.
Source: Stacks 07A6 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev dAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : g B f ⊣ r B f :=
  (clopenModuleAdj B f).mapDerivedCategoryRightDerivedAdjunction

/-- The exact single-level open adjunction, with its original unit and counit.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def dJAdj {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] : j B f ⊣ g B f :=
  (moduleJAdj B f).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (modulePullback B f).rightDerivedFunctorIsoMapDerivedCategory

/-- Exact descent of the specified ordinary alpha, with both composition factors.
Source: Stacks 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def singleDerivedAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) : j B i ⋙ g B p ⟶ g B f ⋙ j B k :=
  (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules B S) (.up ℤ))
      ((moduleJ B i ⋙ modulePullback B p).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((modulePullback B f ⋙ moduleJ B k).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (moduleJ B i ⋙ modulePullback B p).mapDerivedCategory
      (modulePullback B f ⋙ moduleJ B k).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (singleAlpha B k f p i h) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso _ _).inv

/-- The single-level proper mate of the same clopen projector.
Source: Stacks 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def singleDerivedGamma {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) : r B f ⋙ j B i ⟶ j B k ⋙ r B p :=
  mateEquiv (dAdj B f) (dAdj B p) (singleDerivedAlpha B k f p i h)

/-- The existing exact evaluation factorization with the original coefficient universe.
Source: Stacks 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def evaluationFactors (X : Scheme.{u}) (n : ℕ) :=
  @Functor.mapDerivedCategoryFactors (Towers B X) inferInstance
    (clopenTowerAbelian B X) (towers_hasDerivedCategory B X)
    (Modules B X) inferInstance (modulesAbelian B X)
    (inferInstance : HasDerivedCategory (Modules B X))
    ((evaluation ℕᵒᵖ (Modules B X)).obj (op n)) inferInstance inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation preserves the same alpha, including the specified clopen section projector.
Source: Stacks 03DI, 03DJ, 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: evaluation commutes termwise with inverse image and extension by zero.
The inverse cartesian beta is characterized by the pulled-back open unit. The clopen
projector theorem identifies pi with the first-factor section projection and with
unit followed by the inverse of openToR. Evaluation retains this projector and the
unit-preserving compositors. Descend these exact identities and compose the factors. -/
theorem evaluation_alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) (n : ℕ) (M : Derived B S) :
    (ev B W n).map ((alpha B k f p i h).app M) ≫
        (evalJ B k n).hom.app ((G B f).obj M) ≫
        (j B k).map ((evalG B f n).hom.app M) =
      (evalG B p n).hom.app ((J B i).obj M) ≫
        (g B p).map ((evalJ B i n).hom.app M) ≫
        (singleDerivedAlpha B k f p i h).app ((ev B S n).obj M) := by
  have hα := exactSquare_unique (towerJ B i) (towerPullback B p)
    (towerPullback B f) (towerJ B k) (towerAlpha B k f p i h) (alpha B k f p i h)
    (alpha_eq_localized_singleAlpha B k f p i h)
  have he := evalD_square_trans (moduleJ B i) (modulePullback B p)
    (modulePullback B f) (moduleJ B k) (singleAlpha B k f p i h) M n
  rw [hα, evalJ_eq, evalJ_eq, evalG_eq, evalG_eq]
  exact he

/-- Evaluation carries the proper mate to the single-level mate of the same projector.
Source: Stacks 07A7, 0D6E (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: apply evaluation to the three factors in gamma_formula. Replace the evaluated
unit and counit by their single-level versions using evaluation_transpose and the
normalized direct-image comparison. Replace alpha using evaluation_alpha. Functoriality
preserves their ordered composite, giving exactly the single-level mate formula. -/
theorem evaluation_gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) (n : ℕ) (M : Derived B V) :
    (ev B T n).map ((gamma B k f p i h).app M) ≫
        (evalR B p n).app ((J B k).obj M) ≫
        (r B p).map ((evalJ B k n).hom.app M) =
      (evalJ B i n).hom.app ((R B f).obj M) ≫
        (j B i).map ((evalR B f n).app M) ≫
        (singleDerivedGamma B k f p i h).app ((ev B V n).obj M) := by
  apply exchangeMate_cube (adj B f) (adj B p) (dAdj B f) (dAdj B p)
    (ev B S n) (ev B V n) (ev B T n) (ev B W n)
    (evalG B f n) (evalJ B i n) (evalJ B k n) (evalG B p n)
    (alpha B k f p i h) (singleDerivedAlpha B k f p i h) (fun X ↦ ?_) M
  apply (cancel_epi ((g B p).map ((evalJ B i n).hom.app X))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono ((evalJ B k n).hom.app ((G B f).obj X) ≫
    (j B k).map ((evalG B f n).hom.app X))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(j B k).map_id, Category.comp_id]
  apply (cancel_epi ((evalG B p n).hom.app ((J B i).obj X))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simpa only [Category.assoc] using evaluation_alpha B k f p i h n X

variable {B} {Λ : Type (u + 1)} [CommRing Λ]

/-- Apply the existing constant-sheaf functor to the coefficient homomorphism.
Source: Stacks 0H7J (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def coefficientMap (φ : B →+* Λ) (X : Scheme.{u}) : coefficients B X ⟶ coefficients Λ X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)

/-- Constant-section identifications commute with any coefficient homomorphism.
Source: Stacks 0H7J, 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the tower realization theorem's coefficient-naturality clause computes both
adjoints on a constant section b as the constant section φ(b). Sheafification's
universal property gives equality, and taking inverse-image adjoints gives this square. -/
theorem coefficient_square (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantRingIso B f).hom ≫ coefficientMap φ X =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap φ Y) ≫
        (constantRingIso Λ f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom φ)).symm

/-- The recorded sectionwise restriction functor for the actual constant ring-sheaf map.
Source: Stacks 03DA (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev moduleRes (φ : B →+* Λ) (X : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap φ X)

/-- Exactness on kernels, before localization.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance moduleRes_limits (φ : B →+* Λ) (X : Scheme.{u}) :
    PreservesFiniteLimits (moduleRes φ X) :=
  (Scheme.proEtaleRingRestrictScalars_properties (coefficientMap φ X)).1

/-- Exactness on cokernels, before localization.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance moduleRes_colimits (φ : B →+* Λ) (X : Scheme.{u}) :
    PreservesFiniteColimits (moduleRes φ X) :=
  (Scheme.proEtaleRingRestrictScalars_properties (coefficientMap φ X)).2.1

/-- Exact descent of scalar restriction, on ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev Res (φ : B →+* Λ) (X : Scheme.{u}) :
    DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules B X) :=
  (moduleRes φ X).mapDerivedCategory

/-- The canonical ordinary scalar/inverse-image comparison, with direction as displayed.
Source: Stacks 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarGModule (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback Λ f ⋙ moduleRes φ X ≅ moduleRes φ Y ⋙ modulePullback B f :=
  (@asIso _ _ _ _
    (Scheme.proEtaleRingRestrictionPullbackInv f (coefficients B Y) (coefficients Λ Y)
      (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
      (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f (coefficients B Y) (coefficients Λ Y)
      (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
      (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f))).symm

/-- The canonical inverse-image scalar comparison after exact descent.
Source: Stacks 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarG (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    g Λ f ⋙ Res φ X ≅ Res φ Y ⋙ g B f :=
  Scheme.proEtaleRingRestrictionDerivedPullback f (coefficients B Y) (coefficients Λ Y)
    (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
    (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f)

/-- The ordinary open comparison in the inverse direction, fixed by its open-unit transpose.
Source: Stacks 03DI (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJInv (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    moduleRes φ U ⋙ moduleJ B f ⟶ moduleJ Λ f ⋙ moduleRes φ X :=
  ((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm (scalarGModule φ f).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The open-unit transpose is invertible for arbitrary coefficient maps.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: identify the pro-etale open site with the slice. Apply
lem-cbc-ringed-open-scalar-adjunction: on the extension presheaf every direct-sum
summand is unchanged, its map is identity, and the remaining values are zero.
The theorem preserves the open units and counits, so uniqueness of transpose
identifies its inverse with scalarJInv. No flatness is needed. -/
theorem scalarJInv_app_isIso (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (M : Modules Λ U) :
    IsIso ((scalarJInv φ f).app M) := by
  have hIso : IsIso (FiniteOpenScalars.openResMap φ f) := by
    -- Paste through fixed coefficient coordinates, then take open inverse mates.
    let α := TwoSquare.mk _ _ _ _ (FiniteOpenScalars.pullRes φ f).hom
    let β := FiniteOpenScalars.fixedPull (A := B) f
    let γ := FiniteOpenScalars.fixedPull (A := Λ) f
    let δ := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom
    have : IsIso α := by dsimp only [α, TwoSquare.mk]; infer_instance
    have : IsIso β := FiniteOpenScalars.fixedPull_isIso f
    have : IsIso γ := FiniteOpenScalars.fixedPull_isIso f
    have : IsIso δ := by dsimp only [δ, TwoSquare.mk]; infer_instance
    have : IsIso (TwoSquare.hComp γ δ) := by
      dsimp only [TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let oa := moduleJAdj Λ f
    let ob := moduleJAdj B f
    let oc := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) f
    let od := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) f
    have := fixedRestriction_equivalence B U
    have := fixedRestriction_equivalence B X
    have := fixedRestriction_equivalence Λ U
    have := fixedRestriction_equivalence Λ X
    have : IsIso ((mateEquiv oa od).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv γ))) :=
      inverseMate_isIso_of_equivalences oa od _
    have : IsIso ((mateEquiv od oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv δ))) := by
      simp only [δ, TwoSquare.mk, IsIso.Iso.inv_hom]
      rw [← scalarPullbackModel_eq B f Λ φ]
      exact scalarOpenModel_isIso B f Λ φ
    have hw : IsIso ((mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _
          (CategoryTheory.inv (TwoSquare.hComp γ δ)))) := by
      rw [inv_hComp, inverseMate_vComp oa od oc]
      dsimp only [TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let w := TwoSquare.mk _ _ _ _ (CategoryTheory.inv (TwoSquare.hComp γ δ))
    let t := TwoSquare.hComp α β
    have : IsIso t := by
      dsimp only [t, TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let z := Functor.isoWhiskerRight (FiniteOpenScalars.resFixed φ X) _ ≪≫
      asIso (TwoSquare.hComp γ δ) ≪≫
      Functor.isoWhiskerLeft (modulePullback Λ f) (FiniteOpenScalars.resFixed φ U).symm
    have ht : CategoryTheory.inv t =
        ((w.whiskerRight (FiniteOpenScalars.resFixed φ U).hom).whiskerLeft
          (FiniteOpenScalars.resFixed φ X).inv) := by
      have hz : t = z.hom :=
        (FiniteOpenScalars.resPull_fixed φ f)
      calc
        CategoryTheory.inv t = CategoryTheory.inv z.hom :=
          IsIso.inv_eq_inv.mpr hz
        _ = _ := by
          simp only [IsIso.Iso.inv_hom, z, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
            Functor.isoWhiskerRight_inv, Iso.symm_inv, asIso_inv, w,
            TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc]
    have hi : IsIso ((mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t))) := by
      rw [ht]
      exact inverseMate_iso_edges oa oc (FiniteOpenScalars.resFixed φ U)
        (FiniteOpenScalars.resFixed φ X).symm w
    let x := (mateEquiv oa ob).symm (TwoSquare.mk _ _ _ _ (FiniteOpenScalars.pullRes φ f).inv)
    let y := (mateEquiv ob oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β))
    have : IsIso y := inverseMate_isIso_of_equivalences ob oc _
    have he : (mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t)) = TwoSquare.hComp x y := by
      dsimp only [t]
      rw [inv_hComp]
      exact inverseMate_vComp oa ob oc _ _
    rw [he] at hi
    exact isIso_of_hComp x y
  change IsIso ((FiniteOpenScalars.openResMap φ f).app M)
  have := hIso
  infer_instance

set_option linter.style.haveILetI false in
theorem scalarJInv_isIso (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] : IsIso (scalarJInv φ f) := by
  letI : ∀ M : Modules Λ U, IsIso ((scalarJInv φ f).app M) :=
    fun M ↦ scalarJInv_app_isIso φ f M
  exact NatIso.isIso_of_isIso_app _

/-- The canonical section-normalized ordinary open scalar comparison.
Source: Stacks 03DI (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJModule (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    moduleJ Λ f ⋙ moduleRes φ X ≅ moduleRes φ U ⋙ moduleJ B f :=
  (@asIso _ _ _ _ (scalarJInv φ f) (scalarJInv_isIso φ f)).symm

/-- Exact descent of the same identity on extension presheaves.
Source: Stacks 03DI, 03DJ, 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJ (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    j Λ f ⋙ Res φ X ≅ Res φ U ⋙ j B f :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (scalarJModule φ f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar comparisons preserve the specified ordinary open unit and counit.
These equations normalize the identity on extension-presheaf generators.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the slice scalar theorem identifies each generator with the same section in
the same summand, and sends the open unit and counit to themselves. Transport
through weakly-etale localization and uniqueness of the unit-preserving adjoint.
These are exactly the two equations of RingedOpenScalar.Equations. -/
theorem scalar_open_normalized (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] :
    ((∀ N : Modules Λ U,
      (moduleRes φ U).map ((moduleJAdj Λ f).unit.app N) ≫
        (scalarGModule φ f).hom.app ((moduleJ Λ f).obj N) ≫
        (modulePullback B f).map ((scalarJModule φ f).hom.app N) =
      (moduleJAdj B f).unit.app ((moduleRes φ U).obj N)) ∧
    (∀ Q : Modules Λ X,
      (scalarJModule φ f).hom.app ((modulePullback Λ f).obj Q) ≫
        (moduleJ B f).map ((scalarGModule φ f).hom.app Q) ≫
        (moduleJAdj B f).counit.app ((moduleRes φ X).obj Q) =
      (moduleRes φ X).map ((moduleJAdj Λ f).counit.app Q))) ∧
    ((∀ N : DerivedCategory (Modules Λ U),
      (Res φ U).map ((dJAdj Λ f).unit.app N) ≫
        (scalarG φ f).hom.app ((j Λ f).obj N) ≫
        (g B f).map ((scalarJ φ f).hom.app N) =
      (dJAdj B f).unit.app ((Res φ U).obj N)) ∧
    (∀ Q : DerivedCategory (Modules Λ X),
      (scalarJ φ f).hom.app ((g Λ f).obj Q) ≫
        (j B f).map ((scalarG φ f).hom.app Q) ≫
        (dJAdj B f).counit.app ((Res φ X).obj Q) =
      (Res φ X).map ((dJAdj Λ f).counit.app Q))) := by
  have hm : ((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm
      (TwoSquare.mk _ _ _ _ (scalarGModule φ f).hom)) =
      (scalarJModule φ f).inv := rfl
  have he := SheafOfModules.RingedOpenScalar.equations_of_inverseMate
    (scalarJModule φ f) (scalarGModule φ f).symm
    (moduleJAdj Λ f) (moduleJAdj B f) hm
  refine ⟨he, ?_⟩
  have hu (K : DerivedCategory (Modules Λ U)) := exact_mate
    (moduleJAdj Λ f) (moduleJAdj B f) (scalarGModule φ f) (scalarJModule φ f).symm
    (dJAdj Λ f) (dJAdj B f)
    (by intro L; simpa only [exactAdj, dJAdj] using exactAdj_unit (moduleJAdj Λ f) L)
    (by intro L; simpa only [exactAdj, dJAdj] using exactAdj_unit (moduleJAdj B f) L)
    (by
      intro L
      have hh := unit_mateEquiv_symm (moduleJAdj Λ f) (moduleJAdj B f)
        (TwoSquare.mk _ _ _ _ (scalarGModule φ f).hom) L
      change _ = _ ≫ (modulePullback B f).map
        (((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm
          (TwoSquare.mk _ _ _ _ (scalarGModule φ f).hom)).app L) at hh
      rw [hm] at hh
      exact hh.symm) K
  apply SheafOfModules.RingedOpenScalar.equations_of_inverseMate
    (scalarJ φ f) (scalarG φ f).symm (dJAdj Λ f) (dJAdj B f)
  ext K
  apply ((dJAdj B f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu' : (dJAdj B f).unit.app ((Res φ U).obj K) ≫
      (g B f).map ((scalarJ φ f).inv.app K) =
    (Res φ U).map ((dJAdj Λ f).unit.app K) ≫
      (scalarG φ f).hom.app ((j Λ f).obj K) := by
    have hG : scalarG φ f =
        Functor.mapDerivedCategorySquareIso (scalarGModule φ f) := by rfl
    rw [hG]
    simpa only [scalarJ, Functor.mapDerivedCategorySquareIso, Iso.trans_inv,
      Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using hu K
  exact (unit_mateEquiv_symm (dJAdj Λ f) (dJAdj B f)
    (TwoSquare.mk _ _ _ _ (scalarG φ f).hom) K).symm.trans hu'.symm

section ScalarCalculations

attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback

attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars

private theorem moduleRes_eq (φ : B →+* Λ) (X : Scheme.{u}) :
    moduleRes φ X = FiniteOpenScalars.res φ X := rfl

private theorem scalarGModule_eq (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarGModule φ f = (FiniteOpenScalars.pullRes φ f).symm := rfl

attribute [local irreducible] scalarGModule

section ScalarCompatibility

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  {u₀ : A₀ ⥤ B₀} {u₁ : A₁ ⥤ B₁} {u₂ : A₂ ⥤ B₂}
  {F G H : A₀ ⥤ A₁} {F' G' H' : B₀ ⥤ B₁}

private theorem scalarPaste_naturality {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') {M N : A₀} (f : M ⟶ N) :
    u₂.map (P.map (F.map f)) ≫ (b.hom.app (F.obj N) ≫ P'.map (a.hom.app N)) =
      (b.hom.app (F.obj M) ≫ P'.map (a.hom.app M)) ≫ P'.map (F'.map (u₀.map f)) := by
  have ha := a.hom.naturality f
  have hb := b.hom.naturality (F.map f)
  dsimp only [Functor.comp_map] at ha hb
  rw [← Category.assoc, hb, Category.assoc, ← P'.map_comp, ha, P'.map_comp,
    Category.assoc]

private def scalarPaste {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') :
    (F ⋙ P) ⋙ u₂ ≅ u₀ ⋙ (F' ⋙ P') :=
  NatIso.ofComponents (fun M ↦ b.app (F.obj M) ≪≫ P'.mapIso (a.app M))
    (fun f ↦ scalarPaste_naturality a b f)

private theorem scalarPaste_hom {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') (M : A₀) :
    (scalarPaste a b).hom.app M = b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) := rfl

private theorem scalarPaste_inv {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') (M : A₀) :
    (scalarPaste a b).inv.app M = P'.map (a.inv.app M) ≫ b.inv.app (F.obj M) := rfl

private def ScalarCompatible (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G') : Prop :=
  ∀ M, u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M)

private theorem scalarCompatible_apply
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'}
    {t : F ⟶ G} {t' : F' ⟶ G'} (h : ScalarCompatible t t' a b) (M : A₀) :
    u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M) := h M

private theorem scalarCompatible_of_inverse
    (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G')
    (h : ∀ M, a.inv.app M ≫ u₁.map (t.app M) = t'.app (u₀.obj M) ≫ b.inv.app M) :
    ScalarCompatible t t' a b := by
  intro M
  apply (cancel_epi (a.inv.app M)).1
  apply (cancel_mono (b.inv.app M)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj] using h M

private theorem scalarCompatible_identity (a : F ⋙ u₁ ≅ u₀ ⋙ F') :
    ScalarCompatible (𝟙 F) (𝟙 F') a a := by
  intro M
  dsimp only [Functor.comp_obj]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

private theorem scalarCompatible_of_id (a : F ⋙ u₁ ≅ u₀ ⋙ F')
    (t : F ⟶ F) (t' : F' ⟶ F') (ht : t = 𝟙 F) (ht' : t' = 𝟙 F') :
    ScalarCompatible t t' a a := by
  subst t
  subst t'
  exact scalarCompatible_identity a

private theorem scalarCompatible_transport {I : Type*}
    (L : I → (A₀ ⥤ A₁)) (L' : I → (B₀ ⥤ B₁))
    (a : ∀ x, L x ⋙ u₁ ≅ u₀ ⋙ L' x)
    (t : ∀ {x y : I}, x = y → (L x ⟶ L y))
    (t' : ∀ {x y : I}, x = y → (L' x ⟶ L' y))
    (ht : ∀ x, t (rfl : x = x) = 𝟙 (L x))
    (ht' : ∀ x, t' (rfl : x = x) = 𝟙 (L' x))
    {x y : I} (h : x = y) : ScalarCompatible (t h) (t' h) (a x) (a y) := by
  subst y
  exact scalarCompatible_of_id (a x) _ _ (ht x) (ht' x)

private theorem scalarCompatible_comp
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {c : H ⋙ u₁ ≅ u₀ ⋙ H'}
    {t : F ⟶ G} {t' : F' ⟶ G'} {s : G ⟶ H} {s' : G' ⟶ H'}
    (ht : ScalarCompatible t t' a b) (hs : ScalarCompatible s s' b c) :
    ScalarCompatible (t ≫ s) (t' ≫ s') a c := by
  intro M
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [hs M, reassoc_of% (ht M)]

private theorem scalarCompatible_inv
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {e : F ≅ G} {e' : F' ≅ G'}
    (h : ScalarCompatible e.hom e'.hom a b) :
    ScalarCompatible e.inv e'.inv b a := by
  intro M
  apply (cancel_epi (u₁.map (e.hom.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (h M), Iso.hom_inv_id_app, Category.comp_id]

private theorem scalarCompatible_whiskerLeft
    {P : A₂ ⥤ A₀} {P' : B₂ ⥤ B₀} (c : P ⋙ u₀ ≅ u₂ ⋙ P')
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {t : F ⟶ G} {t' : F' ⟶ G'}
    (h : ScalarCompatible t t' a b) :
    ScalarCompatible (Functor.whiskerLeft P t) (Functor.whiskerLeft P' t')
      (scalarPaste c a) (scalarPaste c b) := by
  intro M
  simp only [Functor.whiskerLeft_app, scalarPaste_hom, Category.assoc]
  rw [reassoc_of% (h (P.obj M))]
  exact congrArg (a.hom.app (P.obj M) ≫ ·) (t'.naturality (c.hom.app M)).symm

private theorem scalarCompatible_whiskerRight
    {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂} (c : P ⋙ u₂ ≅ u₁ ⋙ P')
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {t : F ⟶ G} {t' : F' ⟶ G'}
    (h : ScalarCompatible t t' a b) :
    ScalarCompatible (Functor.whiskerRight t P) (Functor.whiskerRight t' P')
      (scalarPaste a c) (scalarPaste b c) := by
  intro M
  have hn := c.hom.naturality (t.app M)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.whiskerRight_app, scalarPaste_hom, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, h M, Functor.map_comp]

private theorem scalarPaste_refl_right (a : F ⋙ u₁ ≅ u₀ ⋙ F') :
    scalarPaste (P := 𝟭 A₁) (P' := 𝟭 B₁) a (Iso.refl u₁) = a := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [scalarPaste_hom, Iso.refl_hom, NatTrans.id_app,
    Functor.id_map]
  erw [Category.id_comp]

private theorem scalarCompatible_projector
    {P : A₁ ⥤ A₀} {P' : B₁ ⥤ B₀}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₀ ≅ u₁ ⋙ P')
    (t : 𝟭 A₀ ⟶ F ⋙ P) (t' : 𝟭 B₀ ⟶ F' ⋙ P')
    (h : ∀ M, u₀.map (t.app M) ≫ b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) =
      t'.app (u₀.obj M)) :
    ScalarCompatible (u₀ := u₀) (u₁ := u₀) (F := 𝟭 A₀) (F' := 𝟭 B₀)
      t t' (Iso.refl u₀) (scalarPaste a b) := by
  intro M
  simp only [scalarPaste_hom, Iso.refl_hom, NatTrans.id_app]
  exact (h M).trans (Category.id_comp _).symm

private theorem scalarCompatible_associator
    {A₃ B₃ : Type*} [Category A₃] [Category B₃]
    {u₃ : A₃ ⥤ B₃} {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    {Q : A₂ ⥤ A₃} {Q' : B₂ ⥤ B₃}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P')
    (c : Q ⋙ u₃ ≅ u₂ ⋙ Q') :
    ScalarCompatible (Functor.associator F P Q).hom
      (Functor.associator F' P' Q').hom
      (scalarPaste (scalarPaste a b) c) (scalarPaste a (scalarPaste b c)) := by
  intro M
  simp only [Functor.associator_hom_app, CategoryTheory.Functor.map_id,
    scalarPaste_hom, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]

private def scalarAlphaPaste
    {A₃ A₄ : Type*} [Category A₃] [Category A₄]
    (Q : A₀ ⥤ A₁) (S : A₁ ⥤ A₂) (J : A₂ ⥤ A₁) (K : A₁ ⥤ A₃)
    (I : A₀ ⥤ A₄) (P : A₄ ⥤ A₃) (L : A₀ ⥤ A₂) (E : A₂ ⥤ A₃)
    (π : 𝟭 A₁ ⟶ S ⋙ J) (β : I ⋙ P ⟶ Q ⋙ K)
    (jc : J ⋙ K ⟶ E) (gc : Q ⋙ S ⟶ L) : I ⋙ P ⟶ L ⋙ E :=
  β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) K ≫
    Functor.whiskerRight (Functor.associator Q S J).inv K ≫
    (Functor.associator (Q ⋙ S) J K).hom ≫
    Functor.whiskerLeft (Q ⋙ S) jc ≫ Functor.whiskerRight gc E

private theorem scalarCompatible_six
    {A₃ A₄ B₃ B₄ : Type*} [Category A₃] [Category A₄] [Category B₃] [Category B₄]
    {u₃ : A₃ ⥤ B₃} {u₄ : A₄ ⥤ B₄}
    (Q : A₀ ⥤ A₁) (Q' : B₀ ⥤ B₁) (S : A₁ ⥤ A₂) (S' : B₁ ⥤ B₂)
    (J : A₂ ⥤ A₁) (J' : B₂ ⥤ B₁) (K : A₁ ⥤ A₃) (K' : B₁ ⥤ B₃)
    (I : A₀ ⥤ A₄) (I' : B₀ ⥤ B₄) (P : A₄ ⥤ A₃) (P' : B₄ ⥤ B₃)
    (L : A₀ ⥤ A₂) (L' : B₀ ⥤ B₂) (E : A₂ ⥤ A₃) (E' : B₂ ⥤ B₃)
    (aQ : Q ⋙ u₁ ≅ u₀ ⋙ Q') (aS : S ⋙ u₂ ≅ u₁ ⋙ S')
    (aJ : J ⋙ u₁ ≅ u₂ ⋙ J') (aK : K ⋙ u₃ ≅ u₁ ⋙ K')
    (aI : I ⋙ u₄ ≅ u₀ ⋙ I') (aP : P ⋙ u₃ ≅ u₄ ⋙ P')
    (aL : L ⋙ u₂ ≅ u₀ ⋙ L') (aE : E ⋙ u₃ ≅ u₂ ⋙ E')
    (π : 𝟭 A₁ ⟶ S ⋙ J) (π' : 𝟭 B₁ ⟶ S' ⋙ J')
    (β : I ⋙ P ⟶ Q ⋙ K) (β' : I' ⋙ P' ⟶ Q' ⋙ K')
    (jc : J ⋙ K ⟶ E) (jc' : J' ⋙ K' ⟶ E')
    (gc : Q ⋙ S ⟶ L) (gc' : Q' ⋙ S' ⟶ L')
    (hπ : ∀ M, u₁.map (π.app M) ≫ aJ.hom.app (S.obj M) ≫ J'.map (aS.hom.app M) =
      π'.app (u₁.obj M))
    (hβ : ScalarCompatible β β' (scalarPaste aI aP) (scalarPaste aQ aK))
    (hj : ScalarCompatible jc jc' (scalarPaste aJ aK) aE)
    (hg : ScalarCompatible gc gc' (scalarPaste aQ aS) aL) :
    ScalarCompatible (scalarAlphaPaste Q S J K I P L E π β jc gc)
      (scalarAlphaPaste Q' S' J' K' I' P' L' E' π' β' jc' gc')
      (scalarPaste aI aP) (scalarPaste aL aE) := by
  unfold scalarAlphaPaste
  have hpi := scalarCompatible_projector aS aJ π π' hπ
  have hpiq := scalarCompatible_whiskerLeft aQ hpi
  rw [scalarPaste_refl_right] at hpiq
  have hpiqb := scalarCompatible_whiskerRight aK hpiq
  have hassoc₁ := scalarCompatible_whiskerRight aK
    (scalarCompatible_inv (e := Functor.associator Q S J)
      (e' := Functor.associator Q' S' J') (scalarCompatible_associator aQ aS aJ))
  have hassoc₂ := scalarCompatible_associator (scalarPaste aQ aS) aJ aK
  have hgj := scalarCompatible_whiskerLeft (scalarPaste aQ aS) hj
  have hgk := scalarCompatible_whiskerRight aE hg
  exact scalarCompatible_comp hβ (scalarCompatible_comp hpiqb
    (scalarCompatible_comp hassoc₁ (scalarCompatible_comp hassoc₂
      (scalarCompatible_comp hgj hgk))))

end ScalarCompatibility

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible

private theorem scalar_pull_comp (φ : B →+* Λ) {U V X : Scheme.{u}}
    (f : U ⟶ V) (g : V ⟶ X) :
    ScalarCompatible (moduleGComp Λ f g).hom (moduleGComp B f g).hom
      (scalarGModule φ (f ≫ g))
      (scalarPaste (scalarGModule φ g) (scalarGModule φ f)) := by
  apply scalarCompatible_of_inverse
  intro M
  have hh := FiniteOpenScalars.pullRes_comp φ f g M
  simpa only [scalarPaste_inv, scalarGModule_eq, Iso.symm_inv,
    moduleRes_eq, Functor.comp_obj, Category.assoc] using hh.symm

private theorem scalarJComp_conjugate (A : Type (u + 1)) [CommRing A]
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    conjugateEquiv ((moduleJAdj A j).comp (moduleJAdj A k))
        (moduleJAdj A (j ≫ k)) (openBetaModuleJComp A j k).inv =
      (moduleGComp A j k).inv :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

section ScalarEquality

attribute [local irreducible] scalarJModule singleJCongr

end ScalarEquality

end ScalarCalculations

section ScalarAlphaCalculations

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible
attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback
attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars
attribute [local irreducible] scalarGModule scalarJModule

private def scalarLiftAlpha (A : Type (u + 1)) [CommRing A]
    {U V W S T : Scheme.{u}} (q : U ⟶ S) (b : U ⟶ W) (s : V ⟶ U)
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (hpb : q ≫ i = b ≫ p) (sq : IsPullback q b i p) (hb : s ≫ b = k) (hq : s ≫ q = f) :
    moduleJ A i ⋙ modulePullback A p ⟶ modulePullback A f ⋙ moduleJ A k :=
  scalarAlphaPaste (modulePullback A q) (modulePullback A s)
    (moduleJ A s) (moduleJ A b) (moduleJ A i) (modulePullback A p)
    (modulePullback A f) (moduleJ A k) (clopenModulePi A s)
    (openBetaModule A q b i p hpb sq).hom
    ((openBetaModuleJComp A s b).hom ≫ (singleJCongr A hb).hom)
    ((moduleGComp A s q).inv ≫ (eqToIso (congrArg (modulePullback A) hq)).hom)

private theorem scalarLiftAlpha_eq (A : Type (u + 1)) [CommRing A]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i) :
    scalarLiftAlpha A (pullback.snd p i) (pullback.fst p i)
        (squareLift k f p i h) k f p i (pullback.condition.symm)
        (IsPullback.of_hasPullback p i).flip (pullback.lift_fst k f h)
        (pullback.lift_snd k f h) = singleAlpha A k f p i h := by
  unfold scalarLiftAlpha scalarAlphaPaste singleAlpha
  rfl

end ScalarAlphaCalculations

end AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars
