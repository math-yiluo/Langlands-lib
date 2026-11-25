/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! The bounded below exchange comparison. -/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

set_option backward.isDefEq.respectTransparency false in
/-- The exchange comparison equation for a bounded below K-injective source complex.
Source: Stacks Project, sites-cohomology.tex, Lemma 0736 and Remark 07A7;
derived.tex, Lemmas 070I, 070K, 0DVC. The comparison is the explicit
argument in step 6 of prose-04-06.

Proof: let N = g^* f_* I. It is bounded below because the termwise functors
preserve zero objects. Express the derived exchange as the adjoint of the
pullback of the derived counit. Naturality of the derived unit moves the source
comparison inside that adjoint. The counit on I is the localized termwise
counit conjugated by s, by uniqueness of the K-injective comparison. The derived
square isomorphism is the termwise square isomorphism conjugated by the exact
inverse-image comparison maps. Substitute both formulas: the adjoint is now
the localization of j composed with the termwise adjoint of the underived
exchange. Compute the derived unit on N by a bounded below injective resolution
of f'^* N. Uniqueness of maps into the K-injective J identifies the resulting
lift with j composed with that termwise adjoint. Apply f'_* to the equality of
homotopy classes and then localize. Naturality of the right-derived unit and
of the counit of injectiveObjectEquivalence identifies the target comparison
with the displayed χ'. This gives the stated equation.
(blueprint: lem-weil-pbc-derived-exchange-bounded-comparison). -/
lemma derivedExchangeBoundedComparison
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective]
    (s : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))
    (J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [J.IsKInjective]
    (j : (((g')^*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j]
    (n : ℤ) [I.IsStrictlyGE n] :
    let B := AddCommGrpCat.{u + 1}
    let C := Sheaf X.smallEtaleTopology B
    let C' := Sheaf X'.smallEtaleTopology B
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient C' (.up ℤ)
    let qY := HomotopyCategory.quotient (Sheaf Y'.smallEtaleTopology B) (.up ℤ)
    let F := (f)_*[B]
    let F' := (f')_*[B]
    let G := (g)^*[B]
    let G' := (g')^*[B]
    let E := DerivedCategory.Plus.injectiveObjectEquivalence C
    let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
    let K' := G'.mapDerivedCategoryPlus.obj K
    let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
    let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
    let ρ := DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)
    let ρ' := DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')
    let t := G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
      DerivedCategory.Qh.map (q'.map j)
    let ex₀ := (NatTrans.mapHomologicalComplex
      (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)).app I
    let e := ex₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j
    ∀ h : ((q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj)),
      s.hom ≫ DerivedCategory.Qh.map h.1 = ρ →
      t ≫ DerivedCategory.Qh.map h.2 = ρ' →
      let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P ≫
          F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
        DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app P' ≫
          F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      let σsrc := G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫ G.mapDerivedCategory.map χ
      σsrc ≫ DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ' := by
  classical
  dsimp only
  intro h hh₁ hh₂
  let H : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ⟨(HomotopyCategory.quotient _ _).obj I, by
      rw [HomotopyCategory.plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩⟩
  let F := (f)_*[AddCommGrpCat.{u + 1}]
  let F' := (f')_*[AddCommGrpCat.{u + 1}]
  let G := (g)^*[AddCommGrpCat.{u + 1}]
  let G' := (g')^*[AddCommGrpCat.{u + 1}]
  let E := DerivedCategory.Plus.injectiveObjectEquivalence
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let E' := DerivedCategory.Plus.injectiveObjectEquivalence
    (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
  let P := (InjectiveObject.ι _).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
  let K' := G'.mapDerivedCategoryPlus.obj K
  let P' := (InjectiveObject.ι _).mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
  let a : K ≅ DerivedCategory.Plus.Qh.obj H :=
    DerivedCategory.Plus.ι.preimageIso s
  have ha : DerivedCategory.Plus.ι.map a.hom = s.hom :=
    DerivedCategory.Plus.ι.map_preimage _
  let h₁ : H ⟶ P := ObjectProperty.homMk h.1
  have hr₁ : DerivedCategory.Plus.Qh.map h₁ ≫ E.counitIso.hom.app K = a.inv := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp]
    change DerivedCategory.Qh.map h.1 ≫ _ = _
    apply (cancel_epi s.hom).1
    rw [← Category.assoc, hh₁]
    have hai : DerivedCategory.Plus.ι.map a.inv = s.inv :=
      DerivedCategory.Plus.ι.map_preimage _
    change DerivedCategory.Plus.ι.map (E.counitIso.inv.app K) ≫
      DerivedCategory.Plus.ι.map (E.counitIso.hom.app K) =
      s.hom ≫ DerivedCategory.Plus.ι.map a.inv
    rw [hai, ← Functor.map_comp]
    simp
  have hc₁ := F.rightDerivedFunctorPlusUnith.naturality h₁
  dsimp only [Functor.comp_map] at hc₁
  have hc₁' : DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P ≫
        F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K)) =
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app H ≫
        F.rightDerivedFunctorPlus.map a.inv) := by
    rw [DerivedCategory.Plus.ι.map_comp, ← Category.assoc]
    change (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map h₁)) ≫ _) ≫ _ = _
    rw [← DerivedCategory.Plus.ι.map_comp, hc₁,
      DerivedCategory.Plus.ι.map_comp, Category.assoc,
      ← DerivedCategory.Plus.ι.map_comp, ← F.rightDerivedFunctorPlus.map_comp, hr₁]
    simp only [Functor.map_comp]
  let h₂ : G'.mapHomotopyCategoryPlus.obj H ⟶ P' :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map j ≫ h.2)
  have hr₂ : DerivedCategory.Plus.Qh.map h₂ ≫ E'.counitIso.hom.app K' =
      G'.mapDerivedCategoryPlusFactorsh.inv.app H ≫
        G'.mapDerivedCategoryPlus.map a.inv := by
    have hG'map : DerivedCategory.Plus.ι.map (G'.mapDerivedCategoryPlus.map a.hom) =
        G'.mapDerivedCategory.map (DerivedCategory.Plus.ι.map a.hom) := rfl
    have hr₂inv : (G'.mapDerivedCategoryPlus.map a.hom ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app H) ≫
        DerivedCategory.Plus.Qh.map h₂ = E'.counitIso.inv.app K' := by
      apply DerivedCategory.Plus.ι.map_injective
      simp only [Functor.map_comp, hG'map,
        G'.ι_map_mapDerivedCategoryPlusFactorsh_hom_app, ha]
      change (G'.mapDerivedCategory.map s.hom ≫
        G'.mapDerivedCategoryFactorsh.hom.app H.obj) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map j ≫ h.2) = _
      rw [DerivedCategory.Qh.map_comp]
      simpa only [Category.assoc] using hh₂
    apply (cancel_epi (G'.mapDerivedCategoryPlus.map a.hom ≫
      G'.mapDerivedCategoryPlusFactorsh.hom.app H)).1
    simp only [Category.assoc] at hr₂inv ⊢
    rw [reassoc_of% hr₂inv]
    simp only [Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc,
      ← G'.mapDerivedCategoryPlus.map_comp, Iso.hom_inv_id]
    rw [G'.mapDerivedCategoryPlus.map_id]
    rfl
  have hc₂ := F'.rightDerivedFunctorPlusUnith.naturality h₂
  dsimp only [Functor.comp_map] at hc₂
  have hc₂' :
      DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map j)) ≫
        (DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
          DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app P' ≫
            F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))) =
      DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app
        (G'.mapHomotopyCategoryPlus.obj H) ≫
        F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app H ≫
          G'.mapDerivedCategoryPlus.map a.inv)) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    rw [DerivedCategory.Plus.ι.map_comp, ← Category.assoc]
    change (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map h₂)) ≫ _) ≫ _ = _
    rw [← DerivedCategory.Plus.ι.map_comp, hc₂,
      DerivedCategory.Plus.ι.map_comp, Category.assoc,
      ← DerivedCategory.Plus.ι.map_comp, ← F'.rightDerivedFunctorPlus.map_comp, hr₂]
    simp only [Functor.map_comp]
  have hn := (Etale.derivedBaseChangeMapPlus
    AddCommGrpCat.{u + 1} sq.toCommSq).naturality a.inv
  change G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlus.map a.inv) ≫
    (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K =
    (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      (DerivedCategory.Plus.Qh.obj H) ≫
      F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlus.map a.inv) at hn
  have hf :
      G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app H) ≫
        (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          (DerivedCategory.Plus.Qh.obj H) =
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj H) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app H) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj H) ≫
        F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app H) :=
    Etale.derivedBaseChangeMapPlus_fac_app AddCommGrpCat.{u + 1} sq.toCommSq H
  have hm :
      (G.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj H) ≫
        G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app H ≫
          F.rightDerivedFunctorPlus.map a.inv)) ≫
        (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K =
      DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus
          (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app H) ≫
        (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj H) ≫
          F'.rightDerivedFunctorPlus.map
            (G'.mapDerivedCategoryPlusFactorsh.inv.app H ≫
              G'.mapDerivedCategoryPlus.map a.inv)) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    rw [reassoc_of% hf]
    simp only [Iso.inv_hom_id_app_assoc]
  have hφG : DerivedCategory.Plus.ι.map
      (G.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj H)) =
      G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj H.obj) := by
    have hφiso : DerivedCategory.Plus.ι.mapIso
        (G.mapDerivedCategoryPlusFactorsh.app (F.mapHomotopyCategoryPlus.obj H)) =
        G.mapDerivedCategoryFactorsh.app
          ((F.mapHomotopyCategory (.up ℤ)).obj H.obj) :=
      Iso.ext (G.ι_map_mapDerivedCategoryPlusFactorsh_hom_app
        (F.mapHomotopyCategoryPlus.obj H))
    exact congrArg Iso.inv hφiso
  have hmi := congrArg DerivedCategory.Plus.ι.map hm
  simp only [Functor.map_comp, hφG] at hmi
  have he :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex
          (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq) (.up ℤ)).app I ≫
            (F'.mapHomologicalComplex (.up ℤ)).map j)) =
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus
          (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app H)) ≫
        DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ _).map j)) := by
    rw [(HomotopyCategory.quotient _ _).map_comp, DerivedCategory.Qh.map_comp]
    rfl
  rw [hc₁', he]
  simp only [Category.assoc]
  erw [hc₂']
  have hGmap₁ : DerivedCategory.Plus.ι.map
      (G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app H)) =
      G.mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app H)) := rfl
  have hGmap₂ : DerivedCategory.Plus.ι.map
      (G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlus.map a.inv)) =
      G.mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map a.inv)) := rfl
  rw [hGmap₁, hGmap₂] at hmi
  simpa only [Functor.map_comp, Category.assoc] using hmi

end AlgebraicGeometry
