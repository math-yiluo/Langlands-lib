/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstantDerivedMapLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Derived mapping sheaves on constant complexes -/

@[expose] public section

universe u
open CategoryTheory Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Opposite

private theorem restrict_map
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {V W : X.Etale} (f : W ⟶ V) (a : K ⟶ L) :
    restrictDerivedMap B f
        ((upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.map a) =
      (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.map a := by
  let r := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) f.left V.hom W.hom f.w.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hn := r.hom.naturality a
  change _ ≫ _ = _ ≫ _ at hn
  change (r.app K).hom ≫ _ ≫ (r.app L).inv = _
  have hh := congrArg (fun k ↦ k ≫ r.inv.app L) hn
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc, Functor.comp_map,
    Iso.hom_inv_id_app, Category.comp_id] using hh.symm

private noncomputable def constantHomMap
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (E G : DerivedCategory (ModuleCat.{u + 1} B)) :
    (Functor.const X.Etaleᵒᵖ).obj (E ⟶ G) ⟶
      derivedHomPresheaf B
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj G)
    where
  app V := ↾fun a ↦ (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.map a)
  naturality V W f := by
    ext a
    exact (restrict_map X B f.unop _).symm

private noncomputable def constantIsoMap
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (E G : DerivedCategory (ModuleCat.{u + 1} B)) :
    (Functor.const X.Etaleᵒᵖ).obj (E ≅ G) ⟶
      derivedIsoPresheaf B
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj G)
    where
  app V := ↾fun a ↦ (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.mapIso
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.mapIso a)
  naturality V W f := by
    ext a
    apply Iso.ext
    exact (restrict_map X B f.unop _).symm

private theorem constant_derived_faithful
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Nonempty X] :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.Faithful := by
  classical
  let x : X := Classical.choice inferInstance
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let F := ((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let e : c.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u + 1} B)) :=
    Functor.mapDerivedCategoryCompIso c F ≪≫
      Functor.mapDerivedCategoryNatIso
        (((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).constantSheafCompSheafFiberIso
          _ _) ≪≫ Functor.mapDerivedCategoryIdIso _
  have : (c.mapDerivedCategory ⋙ F.mapDerivedCategory).Faithful :=
    Functor.Faithful.of_iso e.symm
  exact Functor.Faithful.of_comp c.mapDerivedCategory F.mapDerivedCategory

private theorem constant_restricted_faithful
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] (V : X.Etale) [Nonempty V.left] :
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory).Faithful := by
  let : (constantSheaf ((𝟭 Scheme).obj V.left).smallEtaleTopology
      (ModuleCat.{u + 1} B)).mapDerivedCategory.Faithful :=
    constant_derived_faithful V.left B
  let e := Functor.mapDerivedCategoryCompIso
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (upperStar (ModuleCat.{u + 1} B) V.hom) ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarConstantSheafIso (ModuleCat.{u + 1} B) V.hom)
  exact Functor.Faithful.of_iso e.symm

private theorem constantHomMap_injective
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (E G : DerivedCategory (ModuleCat.{u + 1} B)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantHomMap X B E G) where
  equalizerSieve_mem {V} a b hab := by
    classical
    by_cases hV : Nonempty V.unop.left
    · let := hV
      have := constant_restricted_faithful X B V.unop
      have heq : a = b := Functor.map_injective
        (F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory) hab
      subst b
      simpa only [Presheaf.equalizerSieve_self_eq_top] using X.smallEtaleTopology.top_mem V.unop
    · have : IsEmpty V.unop.left := not_nonempty_iff.mp hV
      exact X.smallEtaleTopology.superset_covering bot_le
        (Scheme.Etale.bot_mem_smallEtaleTopology V.unop)

private theorem constantHomMap_surjective
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantHomMap X B (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G)) where
  imageSieve_mem {V} a := by
    obtain ⟨S, hS, h⟩ :=
      finiteRing_constant_derived_map_local X B E G hE hG hEfin hGfin V a
    apply X.smallEtaleTopology.superset_covering _ hS
    intro W f hf
    obtain ⟨b, hb⟩ := h W f hf
    exact ⟨b, hb.symm⟩

private theorem constantIsoMap_injective
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (E G : DerivedCategory (ModuleCat.{u + 1} B)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantIsoMap X B E G) where
  equalizerSieve_mem {V} a b hab := by
    have hh := congrArg Iso.hom hab
    have h := (constantHomMap_injective X B E G).equalizerSieve_mem a.hom b.hom hh
    apply X.smallEtaleTopology.superset_covering _ h
    intro W f hf
    exact Iso.ext hf

private theorem constantIsoMap_surjective
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantIsoMap X B (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G)) where
  imageSieve_mem {V} e := by
    let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
    let F := c.mapDerivedCategory
    let H := constantHomMap X B (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G)
    let I := constantHomMap X B (DerivedCategory.Q.obj G) (DerivedCategory.Q.obj E)
    have hH := (constantHomMap_surjective X B E G hE hG hEfin hGfin).imageSieve_mem e.hom
    have hI := (constantHomMap_surjective X B G E hG hE hGfin hEfin).imageSieve_mem e.inv
    apply X.smallEtaleTopology.transitive (X.smallEtaleTopology.intersection_covering hH hI)
    intro W f hf
    obtain ⟨a, ha⟩ := hf.1
    obtain ⟨b, hb⟩ := hf.2
    change (constantHomMap X B _ _).app (op W) a = restrictDerivedMap B f e.hom at ha
    change (constantHomMap X B _ _).app (op W) b = restrictDerivedMap B f e.inv at hb
    let R := (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory
    have hab : (constantHomMap X B (DerivedCategory.Q.obj E)
        (DerivedCategory.Q.obj E)).app (op W) (a ≫ b) =
        (constantHomMap X B (DerivedCategory.Q.obj E)
          (DerivedCategory.Q.obj E)).app (op W) (𝟙 _) := by
      change R.map (F.map (a ≫ b)) = R.map (F.map (𝟙 _))
      rw [F.map_comp, R.map_comp, F.map_id, R.map_id]
      change (H.app (op W) a) ≫ (I.app (op W) b) = _
      rw [ha, hb]
      simpa only [restrictDerivedIso, restrictDerivedMap, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
        using (restrictDerivedIso B f e).hom_inv_id
    have hba : (constantHomMap X B (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj G)).app (op W) (b ≫ a) =
        (constantHomMap X B (DerivedCategory.Q.obj G)
          (DerivedCategory.Q.obj G)).app (op W) (𝟙 _) := by
      change R.map (F.map (b ≫ a)) = R.map (F.map (𝟙 _))
      rw [F.map_comp, R.map_comp, F.map_id, R.map_id]
      change (I.app (op W) b) ≫ (H.app (op W) a) = _
      rw [hb, ha]
      simpa only [restrictDerivedIso, restrictDerivedMap, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
        using (restrictDerivedIso B f e).inv_hom_id
    have h₁ := (constantHomMap_injective X B _ _).equalizerSieve_mem (a ≫ b) (𝟙 _) hab
    have h₂ := (constantHomMap_injective X B _ _).equalizerSieve_mem (b ≫ a) (𝟙 _) hba
    apply X.smallEtaleTopology.superset_covering _
      (X.smallEtaleTopology.intersection_covering h₁ h₂)
    intro Z g hg
    let i : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj G := ⟨a, b, hg.1, hg.2⟩
    refine ⟨i, ?_⟩
    apply Iso.ext
    change (constantHomMap X B _ _).app (op Z) a =
      restrictDerivedMap B (g ≫ f) e.hom
    rw [(derivedMapRestriction_laws B _ _).2.1 Z W V g f e.hom]
    rw [← ha]
    exact (restrict_map X B g (F.map a)).symm

private theorem sheaf_iso_of_local
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))] [J.WEqualsLocallyBijective (Type (u + 1))]
    {S : Type (u + 1)} {P : Cᵒᵖ ⥤ Type (u + 1)}
    (f : (Functor.const Cᵒᵖ).obj S ⟶ P)
    (hi : Presheaf.IsLocallyInjective J f) (hs : Presheaf.IsLocallySurjective J f) :
    Nonempty ((presheafToSheaf J (Type (u + 1))).obj P ≅
      (constantSheaf J (Type (u + 1))).obj S) := by
  have : J.W f := (J.W_iff_isLocallyBijective f).2 ⟨hi, hs⟩
  have : IsIso ((presheafToSheaf J (Type (u + 1))).map f) := (J.W_iff f).1 this
  exact ⟨(asIso ((presheafToSheaf J (Type (u + 1))).map f)).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictDerivedMap_comp
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (g : U ⟶ V)
    (a : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L)
    (b : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj M) :
    restrictDerivedMap B g (a ≫ b) = restrictDerivedMap B g a ≫ restrictDerivedMap B g b := by
  simp only [restrictDerivedMap, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictDerivedMap_map
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (g : U ⟶ V) (a : K ⟶ L) :
    restrictDerivedMap B g ((upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.map a) =
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.map a := by
  let r := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) g.left V.hom U.hom g.w.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hn := r.hom.naturality a
  change _ ≫ _ = _ ≫ _ at hn
  change (r.app K).hom ≫ _ ≫ (r.app L).inv = _
  have hh := congrArg (fun k ↦ k ≫ r.inv.app L) hn
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc, Functor.comp_map,
    Iso.hom_inv_id_app, Category.comp_id]
    using hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedHomPresheafIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L K' L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (e : K ≅ K') (f : L ≅ L') :
    derivedHomPresheaf B K L ≅ derivedHomPresheaf B K' L' :=
  NatIso.ofComponents (fun U ↦
    (Iso.homCongr ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso e)
      ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso f)).toIso)
    (by
      intro U V g
      ext a
      symm
      change restrictDerivedMap B g.unop
        ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map e.inv ≫ a ≫
          (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map f.hom) =
        (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map e.inv ≫
          restrictDerivedMap B g.unop a ≫
            (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map f.hom
      rw [restrictDerivedMap_comp, restrictDerivedMap_comp, restrictDerivedMap_map,
        restrictDerivedMap_map])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedIsoPresheafIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L K' L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (e : K ≅ K') (f : L ≅ L') :
    derivedIsoPresheaf B K L ≅ derivedIsoPresheaf B K' L' :=
  NatIso.ofComponents (fun U ↦
    (Iso.isoCongr ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso e)
      ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso f)).toIso)
    (by
      intro U V g
      ext a
      apply Iso.ext
      symm
      change restrictDerivedMap B g.unop
        ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map e.inv ≫ a.hom ≫
          (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map f.hom) =
        (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map e.inv ≫
          restrictDerivedMap B g.unop a.hom ≫
            (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map f.hom
      rw [restrictDerivedMap_comp, restrictDerivedMap_comp, restrictDerivedMap_map,
        restrictDerivedMap_map])

/-- Sheafified derived Hom and Isom between bounded finite constant complexes are the
constant algebraic Hom and Isom sets.

Source: Stacks Project, Tags 09BE and 08FR, and the finite-source argument of
`lem-weil-pbc-finite-ring-derived-local-constancy`, steps 2--7.
(blueprint: lem-weil-pbc-finite-ring-constant-derived-mapping-sheaves)

Proof: Approximate E by a bounded finite free complex with cone strictly below
G. Triangle exactness and orthogonality compare maps from E with maps from that
approximation, both algebraically and after exact constant realization and restriction.
Local-actual and finite componentwise constant-map descent give local algebraic
representatives. An exact geometric stalk retracts constant realization on every
nonempty scheme, proving local uniqueness. Lift an isomorphism and its inverse on a
common cover; local uniqueness makes their algebraic composites identities. Thus both
comparison maps are locally bijective, so sheafification inverts them. Empty schemes,
zero coefficient rings and empty Isom sets are included. -/
theorem finiteRing_constant_derived_mapping_sheaves
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedHomPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G)) ∧
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedIsoPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj G)) := by
  let c := constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)
  let eE := c.mapDerivedCategoryFactors.app E
  let eG := c.mapDerivedCategoryFactors.app G
  have hH := sheaf_iso_of_local U.smallEtaleTopology
    (constantHomMap U B (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G))
    (constantHomMap_injective U B _ _)
    (constantHomMap_surjective U B E G hE hG hEfin hGfin)
  have hI := sheaf_iso_of_local U.smallEtaleTopology
    (constantIsoMap U B (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G))
    (constantIsoMap_injective U B _ _)
    (constantIsoMap_surjective U B E G hE hG hEfin hGfin)
  constructor
  · exact ⟨(presheafToSheaf U.smallEtaleTopology (Type (u + 1))).mapIso
      (derivedHomPresheafIso U B eE eG).symm ≪≫ hH.some⟩
  · exact ⟨(presheafToSheaf U.smallEtaleTopology (Type (u + 1))).mapIso
      (derivedIsoPresheafIso U B eE eG).symm ≪≫ hI.some⟩

end AlgebraicGeometry.Etale
