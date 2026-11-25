/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory

/-! # Gluing derived complexes and compatible morphisms on two opens

Source: literature/stacks-project/cohomology.tex, Tag 08DG (Lemma 20.45.1)
(blueprint: lem-sc-scheme-derived-hom-restriction-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
section

namespace RestrictionTransport

open CategoryTheory.Functor in
/-- The composition comparison on a complex, with its identity complex comparison removed.
Source: `Functor.mapDerivedCategoryCompIso_fac`.
(blueprint: lem-sc-scheme-derived-hom-restriction-transport). -/
private lemma comp_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
    ext n
    simp
  simpa [h] using mapDerivedCategoryCompIso_fac F G K

open CategoryTheory.Functor in
/-- Solve the composition factorization for its forward comparison on a complex.
Source: `Functor.mapDerivedCategoryCompIso_fac`.
(blueprint: lem-sc-scheme-derived-hom-restriction-transport). -/
private lemma comp_hom_Q
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫
      G.mapDerivedCategoryFactors.inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  rw [← cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  exact comp_fac F G K

open CategoryTheory.Functor in
/-- Solve the composition factorization for its inverse comparison on a complex.
Source: `Functor.mapDerivedCategoryCompIso_fac`.
(blueprint: lem-sc-scheme-derived-hom-restriction-transport). -/
private lemma comp_inv_Q
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  rw [← cancel_epi ((mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K))]
  simp only [Iso.inv_hom_id_app]
  rw [reassoc_of% (comp_fac F G K)]
  simp

open CategoryTheory.Functor in
/-- Solve the natural-isomorphism factorization for its component on a complex.
Source: `Functor.mapDerivedCategoryNatIso_fac`.
(blueprint: lem-sc-scheme-derived-hom-restriction-transport). -/
private lemma nat_hom_Q
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) ≫
      G.mapDerivedCategoryFactors.inv.app K := by
  rw [← cancel_mono (G.mapDerivedCategoryFactors.hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact mapDerivedCategoryNatIso_fac e K

open CategoryTheory.Functor in
/-- Deriving a pasted square agrees with pasting its derived comparison maps.
Source: the factorization laws for exact derived functors and
`Localization.natTrans_ext`. Proof: check after precomposition with the localization.
Expand comparison maps using their factorization laws, move the inner comparison
across the factorization of A by naturality, and cancel inverse pairs. Naturality
of the factorization of v leaves a levelwise equality of complex morphisms.
(blueprint: lem-sc-scheme-derived-hom-restriction-transport). -/
private lemma pasting
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    {H I : Type*} [Category H] [Category I] [Abelian H] [Abelian I]
    [HasDerivedCategory H] [HasDerivedCategory I] (A : C ⥤ D) (e : D ⥤ E) (S : E ⥤ I)
    (T : D ⥤ H) (v : H ⥤ I) (B : C ⥤ H)
    [A.Additive] [e.Additive] [S.Additive] [T.Additive] [v.Additive] [B.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits e] [PreservesFiniteColimits e]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    (κ : e ⋙ S ≅ T ⋙ v) (γ : A ⋙ T ≅ B) :
    let α := associator A e S ≪≫ isoWhiskerLeft A κ ≪≫
      (associator A T v).symm ≪≫ isoWhiskerRight γ v
    let k := mapDerivedCategoryCompIso e S ≪≫ mapDerivedCategoryNatIso κ ≪≫
      (mapDerivedCategoryCompIso T v).symm
    let d := mapDerivedCategoryCompIso A T ≪≫ mapDerivedCategoryNatIso γ
    (mapDerivedCategoryCompIso (A ⋙ e) S).hom ≫
      (mapDerivedCategoryNatIso α).hom ≫ (mapDerivedCategoryCompIso B v).inv =
    whiskerRight (mapDerivedCategoryCompIso A e).inv S.mapDerivedCategory ≫
      whiskerLeft A.mapDerivedCategory k.hom ≫ whiskerRight d.hom v.mapDerivedCategory := by
  dsimp only
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [comp_inv_Q, nat_hom_Q, comp_hom_Q, comp_hom_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  let k := mapDerivedCategoryCompIso e S ≪≫ mapDerivedCategoryNatIso κ ≪≫
    (mapDerivedCategoryCompIso T v).symm
  have hn := k.hom.naturality (A.mapDerivedCategoryFactors.inv.app K)
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  dsimp only [k, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [comp_inv_Q, nat_hom_Q, comp_hom_Q, comp_inv_Q, nat_hom_Q]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
  have hv := v.mapDerivedCategoryFactors.inv.naturality
    ((NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K)
  simp only [CategoryTheory.Functor.comp_map] at hv
  erw [← reassoc_of% hv, ← DerivedCategory.Q.map_comp_assoc]
  have hc : (NatTrans.mapHomologicalComplex
      ((A.isoWhiskerLeft κ).hom ≫ (A.associator T v).inv ≫
        (isoWhiskerRight γ v).hom) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex κ.hom (.up ℤ)).app
        ((A.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (v.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K) := by
    ext n
    simp only [NatTrans.mapHomologicalComplex_app_f, NatTrans.comp_app,
      associator_inv_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    erw [Category.id_comp]
    rfl
  erw [hc]
  rfl

open CategoryTheory.Functor in
/-- Transport morphisms across a pasted square of exact derived functors.
Source: the preceding pasting identity, `Functor.map_preimage`, and naturality.
Proof: map the full preimage back, paste the comparison square, and cancel the
outer comparison isomorphisms. Naturality of the inner square gives the result.
Only fullness of the derived functor is needed.
(blueprint: lem-sc-scheme-derived-hom-restriction-transport). -/
private lemma transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    {H I : Type*} [Category H] [Category I] [Abelian H] [Abelian I]
    [HasDerivedCategory H] [HasDerivedCategory I] (A : C ⥤ D) (e : D ⥤ E) (S : E ⥤ I)
    (T : D ⥤ H) (v : H ⥤ I) (B : C ⥤ H)
    [A.Additive] [e.Additive] [S.Additive] [T.Additive] [v.Additive] [B.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits e] [PreservesFiniteColimits e]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [e.mapDerivedCategory.Full]
    (κ : e ⋙ S ≅ T ⋙ v) (γ : A ⋙ T ≅ B) (F G : DerivedCategory C) :
    let α := associator A e S ≪≫ isoWhiskerLeft A κ ≪≫
      (associator A T v).symm ≪≫ isoWhiskerRight γ v
    let αD := mapDerivedCategoryCompIso (A ⋙ e) S ≪≫ mapDerivedCategoryNatIso α
    let qU := (mapDerivedCategoryCompIso A e).symm
    let qW := (mapDerivedCategoryCompIso B v).symm
    let d := mapDerivedCategoryCompIso A T ≪≫ mapDerivedCategoryNatIso γ
    ∀ (a : (A ⋙ e).mapDerivedCategory.obj F ⟶ (A ⋙ e).mapDerivedCategory.obj G),
      αD.inv.app F ≫ S.mapDerivedCategory.map a ≫ αD.hom.app G =
        qW.hom.app F ≫ v.mapDerivedCategory.map
          (d.inv.app F ≫ T.mapDerivedCategory.map
            (e.mapDerivedCategory.preimage (qU.inv.app F ≫ a ≫ qU.hom.app G)) ≫
            d.hom.app G) ≫ qW.inv.app G := by
  intro α αD qU qW d a
  let k := mapDerivedCategoryCompIso e S ≪≫ mapDerivedCategoryNatIso κ ≪≫
    (mapDerivedCategoryCompIso T v).symm
  have hc (Z : DerivedCategory C) :
      αD.hom.app Z ≫ qW.hom.app Z =
        S.mapDerivedCategory.map (qU.hom.app Z) ≫ k.hom.app (A.mapDerivedCategory.obj Z) ≫
          v.mapDerivedCategory.map (d.hom.app Z) := by
    simpa only [α, αD, qU, qW, k, d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, Category.assoc] using
      congr_app (pasting A e S T v B κ γ) Z
  let b := e.mapDerivedCategory.preimage (qU.inv.app F ≫ a ≫ qU.hom.app G)
  have hb : e.mapDerivedCategory.map b = qU.inv.app F ≫ a ≫ qU.hom.app G :=
    e.mapDerivedCategory.map_preimage _
  change αD.inv.app F ≫ S.mapDerivedCategory.map a ≫ αD.hom.app G =
    qW.hom.app F ≫ v.mapDerivedCategory.map
      (d.inv.app F ≫ T.mapDerivedCategory.map b ≫ d.hom.app G) ≫ qW.inv.app G
  rw [← cancel_epi (αD.hom.app F), ← cancel_mono (qW.hom.app G)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [hc G, ← Category.assoc (αD.hom.app F), hc F]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← v.mapDerivedCategory.map_comp_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  have hqa : a ≫ qU.hom.app G = qU.hom.app F ≫ e.mapDerivedCategory.map b := by
    rw [hb]
    simp only [Iso.hom_inv_id_app_assoc]
  have hn := k.hom.naturality b
  simp only [CategoryTheory.Functor.comp_map] at hn
  rw [← S.mapDerivedCategory.map_comp_assoc, hqa,
    S.mapDerivedCategory.map_comp_assoc, reassoc_of% hn]
end RestrictionTransport

end

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
-- Additivity of the three-fold composite restriction functors exceeds the default size.
-- v4.35 tree: this override is still needed here (green in bumpF build81, whnf timeout without it in build82);
-- master removed it on the pre-bump tree.
set_option maxHeartbeats 1600000 in
-- Elaborating the restriction functors and their comparison isomorphisms needs this budget.
/-- Restricting a local derived morphism commutes with transporting from the localized
site to the open subscheme. The formula includes all derived composition comparisons.
Source: Stacks Project, Cohomology, Tag 08BW, canonical local Hom restriction maps;
Mathlib's equivalence Scheme.Modules.overEquiv
(blueprint: lem-sc-scheme-derived-hom-restriction-transport).
Proof: mapDerivedCategoryCompIso identifies restriction on the open subscheme with
restriction to the localized site followed by the derived equivalence. Transport a
back using the full and faithful derived equivalence and these identifications.
The underived comparison from iterated restriction to direct restriction cancels
the functor and inverse of overEquiv U using its unit. After deriving, the unit
naturality equation cancels the transported equivalence on the morphism a.
Associativity of the derived composition comparisons identifies what remains
with overFunctorMap followed by the equivalence for W. This is precisely the
conjugation defining derivedOpenHomRestriction. Conjugating by the outer
composition comparisons gives the displayed equality. This argument is natural
in F and E and works for W=U and W empty as well. -/
theorem scheme_derived_hom_restriction_transport
    (X : Scheme.{u}) (U W : X.Opens) (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (F E : schemeDerivedCategory X) :
    let R_U := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let S_U := (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
            (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv W)).mapDerivedCategory
    let eU := ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
            (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv W))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
              (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv W))))
    let e := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let eW := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
      (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv W)
    let qU := (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) e).symm
    let qW := (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W) eW).symm
    ∀ (a : R_U.obj F ⟶ R_U.obj E),
      eU.inv.app F ≫ S_U.map a ≫ eU.hom.app E =
        qW.hom.app F ≫ eW.mapDerivedCategory.map
          (derivedOpenHomRestriction X.toRingedSpace i
            (e.mapDerivedCategory.preimage (qU.inv.app F ≫ a ≫ qU.hom.app E))) ≫
          qW.inv.app E := by
  intro R_U S_U eU e eW qU qW a
  let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let B := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
  let T := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i
  let S := Equivalence.inverse
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U) ⋙ T ⋙ eW
  let κ : e ⋙ S ≅ T ⋙ eW :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
        Functor.leftUnitor _
  let γ := SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i
  exact RestrictionTransport.transport A e S T eW B κ γ F E a

end AlgebraicGeometry
