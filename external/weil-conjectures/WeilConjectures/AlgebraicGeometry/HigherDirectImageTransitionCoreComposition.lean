/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions


import WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Higher direct image transition compatibility

Source: Stacks Project, Tags 09Z1 and 03Q8, canonical comparison maps.
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private noncomputable def fastTransition (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      R+((h')_*[ModuleCat.{u + 1} Λ]).obj
        (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h').derivedPlus.unit.app _ ≫
    R+((h')_*[ModuleCat.{u + 1} Λ]).map
      (((eqToIso (congrArg
          (fun t : Y' ⟶ S ↦ ((t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus)
          w.symm)).hom.app _ ≫
        (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app _) ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.counit.app K))

/-- Naturality of the derived comparison in its complex, by naturality of the
unit, composition comparison and counit. Source: Stacks Tag 09Z1. -/
private lemma fastTransition_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫ fastTransition Λ a h h' w L =
      fastTransition Λ a h h' w K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  subst h'
  let A := ModuleCat.{u + 1} Λ
  let adj := (upperStarLowerStarAdjunction A (a ≫ h)).derivedPlus
  let c := upperStarPlusComp A a h
  have ht (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
      fastTransition Λ a h (a ≫ h) rfl M =
        (adj.homEquiv _ _) (c.hom.app (R+((h)_*[A]).obj M) ≫
          D+((a)^*[A]).map
            ((upperStarLowerStarAdjunction A h).derivedPlus.counit.app M)) := by
    simp only [fastTransition, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
    rfl
  rw [ht, ht]
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  dsimp only [A, Functor.id_obj]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn := c.hom.naturality (R+((h)_*[A]).map f)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  have hn' := (upperStarLowerStarAdjunction A h).derivedPlus.counit.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn'
  rw [hn', Functor.map_comp, Category.assoc]

private theorem fastTransition_comp
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Y₁ Y₂ : Scheme.{u}} (h : Y ⟶ X)
    (a₂ : Y₂ ⟶ Y) (h₂ : Y₂ ⟶ X) (wh₂ : a₂ ≫ h = h₂)
    (a₁ : Y₁ ⟶ Y₂) (h₁ : Y₁ ⟶ X) (wh₁ : a₁ ≫ h₂ = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    fastTransition Λ a₂ h h₂ wh₂ K ≫
        fastTransition Λ a₁ h₂ h₁ wh₁
          (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app K) =
      fastTransition Λ (a₁ ≫ a₂) h h₁
        (by rw [Category.assoc, wh₂, wh₁]) K := by
  subst h₂
  subst h₁
  let A := ModuleCat.{u + 1} Λ
  let adj₀ := (Etale.upperStarLowerStarAdjunction A h).derivedPlus
  let adj₂ := (Etale.upperStarLowerStarAdjunction A (a₂ ≫ h)).derivedPlus
  let adj₁ := (Etale.upperStarLowerStarAdjunction A (a₁ ≫ a₂ ≫ h)).derivedPlus
  let c₂ := Etale.upperStarPlusComp A a₂ h
  let c₁ := Iso.refl D+((a₁ ≫ a₂ ≫ h)^*[A]) ≪≫
    Etale.upperStarPlusComp A a₁ (a₂ ≫ h)
  let t₂ := fastTransition Λ a₂ h (a₂ ≫ h) rfl K
  let f₂ := c₂.hom.app (R+((h)_*[A]).obj K) ≫
    D+((a₂)^*[A]).map (adj₀.counit.app K)
  have ht₂ : (adj₂.homEquiv (R+((h)_*[A]).obj K)
      (D+((a₂)^*[A]).obj K)).symm t₂ = f₂ := by
    have he : t₂ = (adj₂.homEquiv (R+((h)_*[A]).obj K)
        (D+((a₂)^*[A]).obj K)) f₂ := by
      simp only [t₂, fastTransition, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
        Category.id_comp]
      rfl
    rw [he]
    exact Equiv.symm_apply_apply _ f₂
  let c := eqToIso (show D+((a₁ ≫ a₂ ≫ h)^*[A]) =
      D+(((a₁ ≫ a₂) ≫ h)^*[A]) by rw [Category.assoc]) ≪≫
    Etale.upperStarPlusComp A (a₁ ≫ a₂) h
  change D+((a₂ ≫ h)^*[A]).map t₂ ≫ adj₂.counit.app _ = f₂ at ht₂
  apply (adj₁.homEquiv _ _).symm.injective
  rw [← Category.assoc t₂, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  change (D+((a₁ ≫ a₂ ≫ h)^*[A]).map t₂ ≫
      (adj₁.homEquiv _ _).symm ((adj₁.homEquiv _ _)
        (c₁.hom.app _ ≫ D+((a₁)^*[A]).map (adj₂.counit.app _)))) ≫
      (Etale.upperStarPlusComp A a₁ a₂).inv.app K =
    (adj₁.homEquiv _ _).symm ((adj₁.homEquiv _ _)
      (c.hom.app _ ≫ D+((a₁ ≫ a₂)^*[A]).map (adj₀.counit.app K)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn := c₁.hom.naturality t₂
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (D+((a₁ ≫ a₂ ≫ h)^*[A]).map t₂), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ht₂]
  dsimp only [f₂]
  rw [Functor.map_comp]
  have ha := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc A a₁ a₂ h
    (a₁ ≫ a₂) (a₂ ≫ h) (a₁ ≫ a₂ ≫ h) rfl rfl (Category.assoc _ _ _).symm)
    (R+((h)_*[A]).obj K)
  simp only [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl,
    Iso.refl_trans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at ha
  have ha' : c₁.hom.app (R+((h)_*[A]).obj K) ≫
      D+((a₁)^*[A]).map (c₂.hom.app _) =
      c.hom.app _ ≫ (Etale.upperStarPlusComp A a₁ a₂).hom.app _ := by
    simpa only [c₁, c₂, c, eqToIso_refl, Iso.refl_trans] using ha
  simp only [Category.assoc]
  rw [← Category.assoc (c₁.hom.app _), ha']
  have hn' := (Etale.upperStarPlusComp A a₁ a₂).inv.naturality (adj₀.counit.app K)
  dsimp only [Functor.comp_map] at hn'
  change D+((a₁)^*[A]).map (D+((a₂)^*[A]).map (adj₀.counit.app K)) ≫
      (Etale.upperStarPlusComp A a₁ a₂).inv.app K =
      (Etale.upperStarPlusComp A a₁ a₂).inv.app
        (D+((h)^*[A]).obj (R+((h)_*[A]).obj K)) ≫
      D+((a₁ ≫ a₂)^*[A]).map (adj₀.counit.app K) at hn'
  simp only [Category.assoc]
  rw [hn']
  simp only [← Category.assoc, Iso.hom_inv_id_app]
  change (c.hom.app (R+((h)_*[A]).obj K) ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]


private lemma transition_eq_fast
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    lowerStarPlusTransition Λ a h h' w K = fastTransition Λ a h h' w K := by
  subst h'
  simp only [lowerStarPlusTransition, fastTransition, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    Iso.trans_hom]

private lemma transition_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫ lowerStarPlusTransition Λ a h h' w L =
      lowerStarPlusTransition Λ a h h' w K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  simpa only [transition_eq_fast] using
    fastTransition_naturality Λ a h h' w f

private theorem transition_comp
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Y₁ Y₂ : Scheme.{u}} (h : Y ⟶ X)
    (a₂ : Y₂ ⟶ Y) (h₂ : Y₂ ⟶ X) (wh₂ : a₂ ≫ h = h₂)
    (a₁ : Y₁ ⟶ Y₂) (h₁ : Y₁ ⟶ X) (wh₁ : a₁ ≫ h₂ = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    lowerStarPlusTransition Λ a₂ h h₂ wh₂ K ≫
        lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁
          (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app K) =
      lowerStarPlusTransition Λ (a₁ ≫ a₂) h h₁
        (by rw [Category.assoc, wh₂, wh₁]) K := by
  simpa only [transition_eq_fast] using
    fastTransition_comp Λ h a₂ h₂ wh₂ a₁ h₁ wh₁ K

private lemma map_inv_hom_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {G H : C ⥤ D} (S : D ⥤ E) (e : G ≅ H) (F : C) :
    S.map (e.inv.app F) ≫ S.map (e.hom.app F) = 𝟙 _ := by
  rw [← S.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

private lemma coefficient_composition
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (B : C ⥤ D) (R₂ : C ⥤ E) (R₁ : D ⥤ E)
    {K L : C} {M N T : D} {P : E}
    (t₂ : P ⟶ R₂.obj K) (t₁ : R₂.obj K ⟶ R₁.obj (B.obj K))
    (t₁' : R₂.obj L ⟶ R₁.obj (B.obj L)) (t₀ : P ⟶ R₁.obj N)
    (c₂ : K ⟶ L) (c₁ : B.obj L ⟶ M) (d : B.obj K ⟶ N)
    (c₀ : N ⟶ T) (e : T ⟶ M) (ei : M ⟶ T) (he : ei ≫ e = 𝟙 M)
    (hn : R₂.map c₂ ≫ t₁' = t₁ ≫ R₁.map (B.map c₂))
    (ht : t₂ ≫ t₁ ≫ R₁.map d = t₀)
    (hc : B.map c₂ ≫ c₁ ≫ ei = d ≫ c₀) :
    (t₀ ≫ R₁.map c₀) ≫ R₁.map e =
      (t₂ ≫ R₂.map c₂) ≫ (t₁' ≫ R₁.map c₁) := by
  have hd : (t₂ ≫ R₂.map c₂) ≫ (t₁' ≫ R₁.map c₁) ≫ R₁.map ei =
      t₀ ≫ R₁.map c₀ := by
    simp only [Category.assoc]
    rw [reassoc_of% hn, ← R₁.map_comp_assoc, ← R₁.map_comp,
      Category.assoc, hc, R₁.map_comp]
    simpa only [Category.assoc] using congrArg (· ≫ R₁.map c₀) ht
  have hh := congrArg (· ≫ R₁.map e) hd.symm
  simpa only [Category.assoc, ← R₁.map_comp, he, CategoryTheory.Functor.map_id,
    Category.comp_id] using hh

private theorem derived_coefficient_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' Y'' : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'')
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (lowerStarPlusTransition Λ (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb])
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      R+((h'')_*[ModuleCat.{u + 1} Λ]).map
        ((((b ≫ a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
      R+((h'')_*[ModuleCat.{u + 1} Λ]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) b a).hom.app F)) =
    (lowerStarPlusTransition Λ a h h' wa
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
    (lowerStarPlusTransition Λ b h' h'' wb
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((a)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      R+((h'')_*[ModuleCat.{u + 1} Λ]).map
        ((((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          (((a)^*[ModuleCat.{u + 1} Λ]).obj F))) := by
  exact coefficient_composition
    D+((b)^*[ModuleCat.{u + 1} Λ])
    R+((h')_*[ModuleCat.{u + 1} Λ]) R+((h'')_*[ModuleCat.{u + 1} Λ])
    (K := D+((a)^*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (L := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[ModuleCat.{u + 1} Λ]).obj F))
    (M := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[ModuleCat.{u + 1} Λ] ⋙ (b)^*[ModuleCat.{u + 1} Λ]).obj F))
    (N := D+((b ≫ a)^*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (T := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((b ≫ a)^*[ModuleCat.{u + 1} Λ]).obj F))
    (P := R+((h)_*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (lowerStarPlusTransition Λ a h h' wa _)
    (lowerStarPlusTransition Λ b h' h'' wb _)
    (lowerStarPlusTransition Λ b h' h'' wb _)
    (lowerStarPlusTransition Λ (b ≫ a) h h''
      (by rw [Category.assoc, wa, wb]) _)
    ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    ((((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
      (((a)^*[ModuleCat.{u + 1} Λ]).obj F))
    ((upperStarPlusComp (ModuleCat.{u + 1} Λ) b a).inv.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    ((((b ≫ a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) b a).hom.app F))
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) b a).inv.app F))
    (map_inv_hom_app (DerivedCategory.Plus.singleFunctor _ 0)
      (upperStarComp (ModuleCat.{u + 1} Λ) b a) F)
    (transition_naturality Λ b h' h'' wb _)
    (transition_comp Λ h a h' wa b h'' wb _)
    (upperStarPlusComp_single Λ b a F)

private lemma map_pasting
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Z) (i : W ⟶ Y) (j : Y ⟶ Z)
    (h : f ≫ g = i ≫ j) : H.map f ≫ H.map g = H.map i ≫ H.map j := by
  rw [← H.map_comp, ← H.map_comp, h]

-- Build congruence proofs before reducing the large derived-category objects.
private meta def congrProofs : Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    let a := a.consumeMData
    let b := b.consumeMData
    if a == b then
      return ← Lean.Meta.mkHEqRefl a
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let fn := e.getAppFn
      let .proj typeName index major := fn | return e
      let info := Lean.getStructureInfo (← Lean.getEnv) typeName
      let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
      return Lean.mkAppN p e.getAppArgs
    let a' ← expandProjection a
    let b' ← expandProjection b
    if a != a' || b != b' then
      return ← congrProofs n a' b'
    let af := a.getAppFn
    let bf := b.getAppFn
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if af != bf || aa.size != ba.size then
      let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
        if f.isConst then
          return (← Lean.getProjectionFnInfo? f.constName!).isSome
        return false
      if !(← isProjection af) then
        if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
          return ← congrProofs n a' b
      if !(← isProjection bf) then
        if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
          return ← congrProofs n a b'
      throwError "different congruence heads: {a} versus {b}"
    let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let args := e.getAppArgs
      if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
        let functor := args[args.size - 2]!
        if functor.isAppOf ``CategoryTheory.Functor.comp then
          let fs := functor.getAppArgs
          let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
            #[fs[fs.size - 2]!, args.back!]
          return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
      return e
    let a' ← expandCompositeObj a
    let b' ← expandCompositeObj b
    if a != a' || b != b' then
      return ← congrProofs n a' b'
    let mut first := 0
    while first < aa.size && aa[first]! == ba[first]! do
      first := first + 1
    let f := Lean.mkAppN af (aa.extract 0 first)
    let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
    let mut args := #[]
    for i in [first:aa.size] do
      let h ← congrProofs n aa[i]! ba[i]!
      let h ← if ct.argKinds[i - first]! == .eq then
        Lean.Meta.mkEqOfHEq h else pure h
      args := args.push aa[i]! |>.push ba[i]! |>.push h
    return Lean.mkAppN ct.proof args

/-- Transitions compose for the canonical pullback coefficients.
Source: Stacks Tag 09Z1, canonical comparisons; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-core-composition).

Proof: use the derived transition composition identity at F[0], then apply homology.
The derived identity follows by applying the inverse h'' adjunction hom-set equivalence:
naturality moves the first transition inside b^*, the h' counit cancels the h' unit,
and associativity of derived pullback comparisons identifies the remaining adjunct
with the one for b≫a. The two degree-zero comparisons compose to the ordinary pullback
comparison, as checked degreewise on the single complex and preserved by localization.
Thus homology gives precisely the displayed comparison. Identity morphisms give the
unit law and zero sheaves give zero maps; no properness or degree bound is required.
-/
theorem higher_direct_image_transition_core_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' Y'' : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImageTransition Λ (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) b a).hom.app F))) =
      higherDirectImageTransition Λ a h h' wa q F ≫
        higherDirectImageTransition Λ b h' h'' wb q
          (((a)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target ← Lean.instantiateMVars (← goal.getType)
      let some (_, lhs, rhs) := target.eq? | throwError "expected equality"
      let C := (← Lean.Meta.inferType lhs).getAppArgs[0]!
      let qExpr := (← Lean.Meta.getLocalDeclFromUserName `q).toExpr
      let H ← Lean.Meta.mkAppM ``DerivedCategory.Plus.homologyFunctor #[C, qExpr]
      let mut inputs := #[]
      for name in [`Λ, `a, `b, `h, `h', `h'', `wa, `wb, `F] do
        inputs := inputs.push (← Lean.Meta.getLocalDeclFromUserName name).toExpr
      let hc ← Lean.Meta.mkAppM ``derived_coefficient_composition inputs
      let some (_, l, r) := (← Lean.Meta.inferType hc).eq?
        | throwError "expected derived equality"
      let la := l.getAppArgs
      let ra := r.getAppArgs
      let proof ← Lean.Meta.mkAppM ``map_pasting
        #[H, la[la.size - 2]!, la[la.size - 1]!,
          ra[ra.size - 2]!, ra[ra.size - 1]!, hc]
      let some (_, lhs', rhs') := (← Lean.Meta.inferType proof).eq?
        | throwError "expected mapped equality"
      let hl ← congrProofs 200 lhs lhs'
      let hr ← congrProofs 200 rhs' rhs
      let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
      let hh ← Lean.Meta.mkAppM ``HEq.trans #[hl, hm]
      let hh ← Lean.Meta.mkAppM ``HEq.trans #[hh, hr]
      goal.assign (← Lean.Meta.mkAppM ``eq_of_heq #[hh])

end AlgebraicGeometry.Etale
