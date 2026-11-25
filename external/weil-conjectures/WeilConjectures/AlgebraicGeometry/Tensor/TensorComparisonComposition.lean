/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.BundledTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.System.SystemCochainTensorReduction
import all WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula

/-! # Composition of representative-normalized tensor comparisons

Source: Stacks 07A4, 06YS, 0G7E and 0G7D.
(blueprint: lem-coef-semilinear-tensor-comparison-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory

attribute [local irreducible] Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

private theorem chain_composition
    {C₀ C₁ C₂ : Type c} [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
    [EssentiallySmall.{max c v r} C₂]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂)
    (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
    (R₂ : Sheaf J₂ CommRingCat.{max c v r})
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₁ R₁)
    (G : Mod.{c, v, max c v r} J₁ R₁ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    (H : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (S₀ : Closed.{c, v, r} J₀ R₀)
    (S₁ : Closed.{c, v, r} J₁ R₁)
    (S₂ : Closed.{c, v, r} J₂ R₂)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (T₂ : Models.{c, v, r} J₂ R₂ S₂)
    (KF : BundledTensorComparison.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁)
    (KG : BundledTensorComparison.{c, v, r} J₁ J₂ R₁ R₂ G S₁ S₂ T₁ T₂)
    (KH : BundledTensorComparison.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂)
    (θ : F ⋙ G ≅ H)
    (ho : ∀ M N,
      G.map (KF.model.ordinary M N).hom ≫
        (KG.model.ordinary (F.obj M) (F.obj N)).hom ≫
        ordinaryTensorHom.{c, v, r} J₂ R₂ (θ.hom.app M) (θ.hom.app N) =
      θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫ (KH.model.ordinary M N).hom)
    (P Q : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ) :
    (totalTensor.{c, v, r} J₂ R₂).map
        (Prod.mkHom (Functor.mapHomologicalComplexCompIsoHomOfIso θ P)
          (Functor.mapHomologicalComplexCompIsoHomOfIso θ Q)) ≫ KH.model.chain P Q =
      KG.model.chain ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (KF.model.chain P Q) ≫
        (Functor.mapHomologicalComplexCompIsoHomOfIso θ
          ((totalTensor.{c, v, r} J₀ R₀).obj (P, Q))) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₂
  let := SheafOfModules.monoidalCategory R₂
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R₂
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R₂
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change tensorSummand.{c, v, r} J₂ R₂ _ _ p q k hpq ≫ _ =
    tensorSummand.{c, v, r} J₂ R₂ _ _ p q k hpq ≫ _
  erw [reassoc_of% tensorSummand_map.{c, v, r} J₂ R₂
    (Functor.mapHomologicalComplexCompIsoHomOfIso θ P)
    (Functor.mapHomologicalComplexCompIsoHomOfIso θ Q) p q k hpq]
  erw [KH.model.summand P Q p q k hpq,
    reassoc_of% (KG.model.summand ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq)]
  change ordinaryTensorHom.{c, v, r} J₂ R₂
      (θ.hom.app (P.X p)) (θ.hom.app (Q.X q)) ≫
      (KH.model.ordinary (P.X p) (Q.X q)).inv ≫
      H.map (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq) =
    ((KG.model.ordinary (F.obj (P.X p)) (F.obj (Q.X q))).inv ≫
      G.map (tensorSummand.{c, v, r} J₁ R₁
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq)) ≫
      G.map ((KF.model.chain P Q).f k) ≫
      θ.hom.app (((totalTensor.{c, v, r} J₀ R₀).obj (P, Q)).X k)
  rw [Category.assoc]
  have hs := KF.model.summand P Q p q k hpq
  have hsF := congrArg G.map hs
  rw [G.map_comp, G.map_comp] at hsF
  rw [reassoc_of% hsF]
  have hn := θ.hom.naturality (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  let u := G.mapIso (KF.model.ordinary (P.X p) (Q.X q)) ≪≫
    KG.model.ordinary (F.obj (P.X p)) (F.obj (Q.X q))
  let w := KH.model.ordinary (P.X p) (Q.X q)
  have hi : u.inv ≫ θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ (P.X p) (Q.X q)) =
      ordinaryTensorHom.{c, v, r} J₂ R₂ (θ.hom.app (P.X p)) (θ.hom.app (Q.X q)) ≫
        w.inv := by
    apply (Iso.inv_comp_eq u).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv w).2
    exact (ho (P.X p) (Q.X q)).symm
  simpa only [u, w, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using
    congrArg (fun z ↦ z ≫ H.map
      (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq)) hi.symm

private theorem derived_on_representatives
    {C₀ C₁ C₂ : Type c} [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
    [EssentiallySmall.{max c v r} C₂]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂)
    (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
    (R₂ : Sheaf J₂ CommRingCat.{max c v r})
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₁ R₁)
    (G : Mod.{c, v, max c v r} J₁ R₁ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    (H : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (S₀ : Closed.{c, v, r} J₀ R₀)
    (S₁ : Closed.{c, v, r} J₁ R₁)
    (S₂ : Closed.{c, v, r} J₂ R₂)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (T₂ : Models.{c, v, r} J₂ R₂ S₂)
    (KF : BundledTensorComparison.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁)
    (KG : BundledTensorComparison.{c, v, r} J₁ J₂ R₁ R₂ G S₁ S₂ T₁ T₂)
    (KH : BundledTensorComparison.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂)
    (θ : F ⋙ G ≅ H)
    (ho : ∀ M N,
      G.map (KF.model.ordinary M N).hom ≫
        (KG.model.ordinary (F.obj M) (F.obj N)).hom ≫
        ordinaryTensorHom.{c, v, r} J₂ R₂ (θ.hom.app M) (θ.hom.app N) =
      θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫ (KH.model.ordinary M N).hom)
    (P Q : CochainComplex (Mod.{c, v, max c v r}
      J₀ R₀) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{c, v, r} J₀ R₀ P) (fQ : flatTerms.{c, v, r} J₀ R₀ Q) :
    let δ := Functor.mapDerivedCategoryCompNatIso θ
    S₂.tensor.map (Prod.mkHom (δ.hom.app (DerivedCategory.Q.obj P))
        (δ.hom.app (DerivedCategory.Q.obj Q))) ≫
      KH.mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    KG.mu.inv.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
      G.mapDerivedCategory.map
        (KF.mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      δ.hom.app (S₀.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  dsimp only
  let δ := Functor.mapDerivedCategoryCompNatIso θ
  let d := Functor.mapHomologicalComplexCompIsoHomOfIso θ
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let GFP := (G.mapHomologicalComplex (.up ℤ)).obj FP
  let GFQ := (G.mapHomologicalComplex (.up ℤ)).obj FQ
  let HP := (H.mapHomologicalComplex (.up ℤ)).obj P
  let HQ := (H.mapHomologicalComplex (.up ℤ)).obj Q
  let Tot := (totalTensor.{c, v, r} J₀ R₀).obj (P, Q)
  let b := twoFactors.{c, v, r} J₀ J₁ J₂ R₀ R₁ R₂ F G
  let r₀ := tensorModelIso.{c, v, r} J₀ R₀ S₀ T₀ P Q hP hQ
  have ffP : flatTerms.{c, v, r} J₁ R₁ FP := fun i ↦
    tensorComparisonModel_preserves_flat J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ KF.mu KF.model
      _ (fP i)
  have ffQ : flatTerms.{c, v, r} J₁ R₁ FQ := fun i ↦
    tensorComparisonModel_preserves_flat J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ KF.mu KF.model
      _ (fQ i)
  have hkGFP := KG.model.kflat FP (KF.model.kflat P hP fP) ffP
  have hkGFQ := KG.model.kflat FQ (KF.model.kflat Q hQ fQ) ffQ
  have hkHP := KH.model.kflat P hP fP
  have hkHQ := KH.model.kflat Q hQ fQ
  let rFG := tensorModelIso.{c, v, r} J₂ R₂ S₂ T₂ GFP GFQ hkGFP hkGFQ
  let rH := tensorModelIso.{c, v, r} J₂ R₂ S₂ T₂ HP HQ hkHP hkHQ
  let cFG := KG.model.chain FP FQ ≫
    (G.mapHomologicalComplex (.up ℤ)).map (KF.model.chain P Q)
  have hFG := fourModels_composite.{c, v, r} J₀ J₁ J₂ R₀ R₁ R₂ F G S₀ S₁ S₂
    T₀ T₁ T₂ KF.mu KG.mu KF.model KG.model P Q hP hQ fP fQ
  have hH := model_inverse.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂ KH.mu KH.model
    P Q hP hQ fP fQ
  change _ = S₂.tensor.map (Prod.mkHom (b P).hom (b Q).hom) ≫
    rFG.inv ≫ DerivedCategory.Q.map cFG at hFG
  change _ = S₂.tensor.map (Prod.mkHom
      (H.mapDerivedCategoryFactors.hom.app P) (H.mapDerivedCategoryFactors.hom.app Q)) ≫
    rH.inv ≫ DerivedCategory.Q.map (KH.model.chain P Q) at hH
  have factors (L : CochainComplex
      (Mod.{c, v, max c v r} J₀ R₀) ℤ) :
      δ.hom.app (DerivedCategory.Q.obj L) ≫ H.mapDerivedCategoryFactors.hom.app L =
      (b L).hom ≫ DerivedCategory.Q.map (d L) := by
    simpa only [b, twoFactors, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using
      Functor.mapDerivedCategoryCompNatIso_hom_app_Q θ L
  have hn := tensorModelIso_naturality.{c, v, r} J₂ R₂ S₂ T₂ GFP HP GFQ HQ
    hkGFP hkHP hkGFQ hkHQ (d P) (d Q)
  change DerivedCategory.Q.map ((totalTensor.{c, v, r} J₂ R₂).map
      (Prod.mkHom (d P) (d Q))) ≫ rH.hom =
    rFG.hom ≫ S₂.tensor.map (Prod.mkHom
      (DerivedCategory.Q.map (d P)) (DerivedCategory.Q.map (d Q))) at hn
  have hinv := congrArg (fun z ↦ rFG.inv ≫ z ≫ rH.inv) hn
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
    Category.comp_id] at hinv
  let z := H.mapDerivedCategory.mapIso r₀.symm ≪≫ H.mapDerivedCategoryFactors.app Tot
  apply (cancel_mono z.hom).1
  simp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  have hδ := δ.hom.naturality r₀.inv
  change G.mapDerivedCategory.map (F.mapDerivedCategory.map r₀.inv) ≫
      δ.hom.app (DerivedCategory.Q.obj Tot) =
    δ.hom.app (S₀.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      H.mapDerivedCategory.map r₀.inv at hδ
  erw [← reassoc_of% hδ]
  erw [factors Tot]
  erw [reassoc_of% hFG]
  erw [hH]
  rw [← S₂.tensor.map_comp_assoc]
  simp only [prod_comp]
  erw [factors P, factors Q]
  erw [← prod_comp (Prod.mkHom (b P).hom (b Q).hom)
    (Prod.mkHom (DerivedCategory.Q.map (d P)) (DerivedCategory.Q.map (d Q))),
    S₂.tensor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hinv]
  simp only [← DerivedCategory.Q.map_comp, ← Category.assoc]
  simpa only [cFG, d, Tot, FP, FQ, Category.assoc] using
    congrArg (fun z ↦ S₂.tensor.map (Prod.mkHom (b P).hom (b Q).hom) ≫ rFG.inv ≫
      DerivedCategory.Q.map z)
    (chain_composition J₀ J₁ J₂ R₀ R₁ R₂ F G H S₀ S₁ S₂ T₀ T₁ T₂ KF KG KH θ ho P Q)

private theorem derived_composition
    {C₀ C₁ C₂ : Type c} [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
    [EssentiallySmall.{max c v r} C₂]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂)
    (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
    (R₂ : Sheaf J₂ CommRingCat.{max c v r})
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₁ R₁)
    (G : Mod.{c, v, max c v r} J₁ R₁ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    (H : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (S₀ : Closed.{c, v, r} J₀ R₀)
    (S₁ : Closed.{c, v, r} J₁ R₁)
    (S₂ : Closed.{c, v, r} J₂ R₂)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (T₂ : Models.{c, v, r} J₂ R₂ S₂)
    (KF : BundledTensorComparison.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁)
    (KG : BundledTensorComparison.{c, v, r} J₁ J₂ R₁ R₂ G S₁ S₂ T₁ T₂)
    (KH : BundledTensorComparison.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂)
    (θ : F ⋙ G ≅ H)
    (ho : ∀ M N,
      G.map (KF.model.ordinary M N).hom ≫
        (KG.model.ordinary (F.obj M) (F.obj N)).hom ≫
        ordinaryTensorHom.{c, v, r} J₂ R₂ (θ.hom.app M) (θ.hom.app N) =
      θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫ (KH.model.ordinary M N).hom)
    (M N : D.{c, v, max c v r} J₀ R₀) :
    let δ := Functor.mapDerivedCategoryCompNatIso θ
    G.mapDerivedCategory.map (KF.mu.hom.app (M, N)) ≫
      KG.mu.hom.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N) ≫
      S₂.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) =
    δ.hom.app (S₀.tensor.obj (M, N)) ≫ KH.mu.hom.app (M, N) := by
  dsimp only
  let δ := Functor.mapDerivedCategoryCompNatIso θ
  let U : (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₂.tensor ⟶
      S₀.tensor ⋙ H.mapDerivedCategory :=
    Functor.whiskerRight (δ.hom.prod δ.hom) S₂.tensor ≫ KH.mu.inv
  let V : (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₂.tensor ⟶
      S₀.tensor ⋙ H.mapDerivedCategory :=
    Functor.whiskerLeft (F.mapDerivedCategory.prod F.mapDerivedCategory) KG.mu.inv ≫
      Functor.whiskerRight KF.mu.inv G.mapDerivedCategory ≫
      Functor.whiskerLeft S₀.tensor δ.hom
  have he : U = V := by
    obtain ⟨_, _, _, h⟩ := SheafOfModules.cochain_tensor_model_rigidity J₀ R₀
    apply (h (D J₂ R₂) inferInstance _ _).1
    apply NatTrans.ext
    funext X
    rcases X with ⟨P, Q⟩
    exact derived_on_representatives J₀ J₁ J₂ R₀ R₁ R₂ F G H S₀ S₁ S₂ T₀ T₁ T₂
      KF KG KH θ ho P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hi := congrArg (fun z ↦ z.app (M, N)) he
  change S₂.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) ≫
      KH.mu.inv.app (M, N) =
    KG.mu.inv.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N) ≫
      G.mapDerivedCategory.map (KF.mu.inv.app (M, N)) ≫
      δ.hom.app (S₀.tensor.obj (M, N)) at hi
  let u := G.mapDerivedCategory.mapIso (KF.mu.app (M, N)) ≪≫
    KG.mu.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N)
  let w := KH.mu.app (M, N)
  have hi' : S₂.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) ≫ w.inv =
      u.inv ≫ δ.hom.app (S₀.tensor.obj (M, N)) := by
    simpa only [u, w, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using hi
  have hf : u.hom ≫ S₂.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) =
      δ.hom.app (S₀.tensor.obj (M, N)) ≫ w.hom := by
    apply (Iso.comp_inv_eq w).1
    rw [Category.assoc, hi', Iso.hom_inv_id_assoc]
  exact (Category.assoc (G.mapDerivedCategory.map (KF.mu.hom.app (M, N)))
    (KG.mu.hom.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N))
    (S₂.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)))).symm.trans hf

/-- Ordinary tensor compatibility implies chain and derived compatibility for exact functors.
Source: Stacks 07A4, 06YS, 0G7E and 0G7D.
(blueprint: lem-coef-semilinear-tensor-comparison-composition).

Proof: test the total-complex equality on each tensor summand. The model summand
formulas and naturality of the compositor reduce it to the inverse ordinary
square. On flat-term K-flat representatives, use the two successive model
comparison equations and the composite comparison equation. The derived
compositor factorization and naturality of the target representative comparison
identify both routes by the chain equality. Cancel the source representative
isomorphism. Cochain tensor model rigidity extends equality from representative
pairs to the whole derived product. Finally invert the comparison square. -/
theorem tensorComparisonComposition
    {C₀ C₁ C₂ : Type c} [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
    [EssentiallySmall.{max c v r} C₂]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂)
    (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
    (R₂ : Sheaf J₂ CommRingCat.{max c v r})
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₁ R₁)
    (G : Mod.{c, v, max c v r} J₁ R₁ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    (H : Mod.{c, v, max c v r} J₀ R₀ ⥤
      Mod.{c, v, max c v r} J₂ R₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (S₀ : Closed.{c, v, r} J₀ R₀)
    (S₁ : Closed.{c, v, r} J₁ R₁)
    (S₂ : Closed.{c, v, r} J₂ R₂)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (T₂ : Models.{c, v, r} J₂ R₂ S₂)
    (KF : BundledTensorComparison.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁)
    (KG : BundledTensorComparison.{c, v, r} J₁ J₂ R₁ R₂ G S₁ S₂ T₁ T₂)
    (KH : BundledTensorComparison.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂)
    (θ : F ⋙ G ≅ H)
    (ho : ∀ M N,
      G.map (KF.model.ordinary M N).hom ≫
        (KG.model.ordinary (F.obj M) (F.obj N)).hom ≫
        ordinaryTensorHom.{c, v, r} J₂ R₂ (θ.hom.app M) (θ.hom.app N) =
      θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫ (KH.model.ordinary M N).hom)
    : (∀ P Q : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ,
      (totalTensor.{c, v, r} J₂ R₂).map
          (Prod.mkHom (Functor.mapHomologicalComplexCompIsoHomOfIso θ P)
            (Functor.mapHomologicalComplexCompIsoHomOfIso θ Q)) ≫ KH.model.chain P Q =
        KG.model.chain ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (KF.model.chain P Q) ≫
          Functor.mapHomologicalComplexCompIsoHomOfIso θ
            ((totalTensor.{c, v, r} J₀ R₀).obj (P, Q))) ∧
      ∀ M N : D.{c, v, max c v r} J₀ R₀,
        G.mapDerivedCategory.map (KF.mu.hom.app (M, N)) ≫
          KG.mu.hom.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N) ≫
          S₂.tensor.map (Prod.mkHom
            ((Functor.mapDerivedCategoryCompNatIso θ).hom.app M)
            ((Functor.mapDerivedCategoryCompNatIso θ).hom.app N)) =
        (Functor.mapDerivedCategoryCompNatIso θ).hom.app (S₀.tensor.obj (M, N)) ≫
          KH.mu.hom.app (M, N) := by
  exact ⟨chain_composition J₀ J₁ J₂ R₀ R₁ R₂ F G H S₀ S₁ S₂ T₀ T₁ T₂ KF KG KH θ ho,
    derived_composition J₀ J₁ J₂ R₀ R₁ R₂ F G H S₀ S₁ S₂ T₀ T₁ T₂ KF KG KH θ ho⟩

end WeilConjectures.SemilinearSections
