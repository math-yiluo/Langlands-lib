/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Localizing a strict square of exact realizations

Consider additive functors `Φ₁ : C ⥤ A₁`, `Φ₀ : C ⥤ A₀`, `τ₁ τ₀ : C ⥤ C'`, a semilinear arrow
`δ : Φ₁ ⟶ Φ₀ ⋙ r` and exact functors `r, u₁, u₀, r', s₁, s₀, o` related by isomorphisms
`p : r ⋙ u₁ ≅ u₀ ⋙ r'`, `c : r' ⋙ s₁ ≅ s₀` and realizations `Bᵢ : Φᵢ ⋙ uᵢ ⋙ sᵢ ≅ τᵢ ⋙ o`.
If the evident square of ordinary functors commutes with `σ : τ₁ ⟶ τ₀`, then on every complex
`P` the localized square, formed with the derived comparison isomorphisms
`Functor.mapDerivedCategoryCompIso` and `Functor.mapDerivedCategoryNatIso`, commutes.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C C' A₁ A₀ B₁ B₀ E : Type*} [Category C] [Category C'] [Category A₁] [Category A₀]
  [Category B₁] [Category B₀] [Category E] [Preadditive C] [Abelian C'] [Abelian A₁]
  [Abelian A₀] [Abelian B₁] [Abelian B₀] [Abelian E]
  [HasDerivedCategory C'] [HasDerivedCategory A₁] [HasDerivedCategory A₀]
  [HasDerivedCategory B₁] [HasDerivedCategory B₀] [HasDerivedCategory E]
  (Φ₁ : C ⥤ A₁) (Φ₀ : C ⥤ A₀) (τ₁ τ₀ : C ⥤ C') [Φ₁.Additive] [Φ₀.Additive]
  [τ₁.Additive] [τ₀.Additive]
  (r : A₀ ⥤ A₁) (u₁ : A₁ ⥤ B₁) (u₀ : A₀ ⥤ B₀) (r' : B₀ ⥤ B₁) (s₁ : B₁ ⥤ E) (s₀ : B₀ ⥤ E)
  (o : C' ⥤ E)
  [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [u₁.Additive] [PreservesFiniteLimits u₁] [PreservesFiniteColimits u₁]
  [u₀.Additive] [PreservesFiniteLimits u₀] [PreservesFiniteColimits u₀]
  [r'.Additive] [PreservesFiniteLimits r'] [PreservesFiniteColimits r']
  [s₁.Additive] [PreservesFiniteLimits s₁] [PreservesFiniteColimits s₁]
  [s₀.Additive] [PreservesFiniteLimits s₀] [PreservesFiniteColimits s₀]
  [o.Additive] [PreservesFiniteLimits o] [PreservesFiniteColimits o]

/-- The localization of a termwise semilinear arrow, as an arrow to the derived restriction. -/
noncomputable def strictSquareArrow (δ : Φ₁ ⟶ Φ₀ ⋙ r) (P : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      r.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ (ComplexShape.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexCompIso (F := Φ₀) (G := r) (Iso.refl _)
        (ComplexShape.up ℤ)).inv.app P) ≫
    r.mapDerivedCategoryFactors.inv.app ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

variable {Φ₁ Φ₀ τ₁ τ₀ r u₁ u₀ r' s₁ s₀ o}

/-- The termwise isomorphism of complexes induced by a realization `Φ ⋙ u ⋙ s ≅ τ ⋙ o`. -/
noncomputable def strictSquareComplexIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] {Φ : C ⥤ A} {τ : C ⥤ C'} {u : A ⥤ B} {s : B ⥤ E}
    [Φ.Additive] [τ.Additive] [u.Additive] [s.Additive]
    (B' : Φ ⋙ u ⋙ s ≅ τ ⋙ o) (P : CochainComplex C ℤ) :
    (s.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((u.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
      (o.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ B'.app (P.X i))
    (fun i j _ ↦ (B'.hom.naturality (P.d i j)).symm)

/-- The localized realization isomorphism of a complex. -/
noncomputable def strictSquareRealization {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    {Φ : C ⥤ A} {τ : C ⥤ C'} {u : A ⥤ B} {s : B ⥤ E}
    [Φ.Additive] [τ.Additive]
    [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (B' : Φ ⋙ u ⋙ s ≅ τ ⋙ o) (P : CochainComplex C ℤ) :
    s.mapDerivedCategory.obj (u.mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≅
      o.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  s.mapDerivedCategory.mapIso (u.mapDerivedCategoryFactors.app _) ≪≫
    s.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (strictSquareComplexIso B' P) ≪≫
    (o.mapDerivedCategoryFactors.app _).symm

set_option backward.isDefEq.respectTransparency false in
/-- A commuting square of ordinary realizations localizes to a commuting square on every
complex. -/
theorem strictSquare_localized (δ : Φ₁ ⟶ Φ₀ ⋙ r) (p : r ⋙ u₁ ≅ u₀ ⋙ r') (c : r' ⋙ s₁ ≅ s₀)
    (B₁ : Φ₁ ⋙ u₁ ⋙ s₁ ≅ τ₁ ⋙ o) (B₀ : Φ₀ ⋙ u₀ ⋙ s₀ ≅ τ₀ ⋙ o) (σ : τ₁ ⟶ τ₀)
    (h : ∀ N : C, s₁.map (u₁.map (δ.app N) ≫ p.hom.app (Φ₀.obj N)) ≫
      c.hom.app (u₀.obj (Φ₀.obj N)) ≫ B₀.hom.app N = B₁.hom.app N ≫ o.map (σ.app N))
    (loc : r.mapDerivedCategory ⋙ u₁.mapDerivedCategory ≅
      u₀.mapDerivedCategory ⋙ r'.mapDerivedCategory)
    (hloc : loc = mapDerivedCategoryCompIso r u₁ ≪≫ mapDerivedCategoryNatIso p ≪≫
      (mapDerivedCategoryCompIso u₀ r').symm)
    (coh : r'.mapDerivedCategory ⋙ s₁.mapDerivedCategory ≅ s₀.mapDerivedCategory)
    (hcoh : coh = mapDerivedCategoryCompIso r' s₁ ≪≫ mapDerivedCategoryNatIso c)
    (P : CochainComplex C ℤ) :
    s₁.mapDerivedCategory.map
        (u₁.mapDerivedCategory.map (strictSquareArrow Φ₁ Φ₀ r δ P) ≫
          loc.hom.app
            (DerivedCategory.Q.obj ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      coh.hom.app
          (u₀.mapDerivedCategory.obj
            (DerivedCategory.Q.obj ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        (strictSquareRealization B₀ P).hom =
      (strictSquareRealization B₁ P).hom ≫
        o.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app P)) := by
  subst hloc hcoh
  let K₀ := (Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let K₁ := (Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let L₀ := (u₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀
  let a : K₁ ⟶ (r.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ :=
    (NatTrans.mapHomologicalComplex δ (ComplexShape.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexCompIso (F := Φ₀) (G := r) (Iso.refl _)
        (ComplexShape.up ℤ)).inv.app P
  let p' : (u₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((r.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ⟶
      (r'.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀ :=
    (NatTrans.mapHomologicalComplex p.hom (ComplexShape.up ℤ)).app K₀
  let c' : (s₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((r'.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀) ⟶
      (s₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀ :=
    (NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app L₀
  set loc := mapDerivedCategoryCompIso r u₁ ≪≫ mapDerivedCategoryNatIso p ≪≫
    (mapDerivedCategoryCompIso u₀ r').symm with hloc_def
  set coh := mapDerivedCategoryCompIso r' s₁ ≪≫ mapDerivedCategoryNatIso c with hcoh_def
  -- the inverse-image comparison on a localized complex
  have hloc : u₁.mapDerivedCategory.map (r.mapDerivedCategoryFactors.inv.app K₀) ≫
      loc.hom.app (DerivedCategory.Q.obj K₀) ≫
      r'.mapDerivedCategory.map (u₀.mapDerivedCategoryFactors.hom.app K₀) ≫
      r'.mapDerivedCategoryFactors.hom.app L₀ =
      u₁.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map p' := by
    have h₀ := mapDerivedCategoryCompIso_hom_app_factors u₀ r' K₀
    have h₁ := (Iso.eq_inv_comp ((mapDerivedCategoryCompIso r u₁).app
      (DerivedCategory.Q.obj K₀))).mp (mapDerivedCategoryCompIso_hom_app_factors r u₁ K₀).symm
    have h₂ := mapDerivedCategoryNatIso_fac p K₀
    simp only [Iso.app_hom] at h₁
    simp only [hloc_def, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [h₀, h₂, reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp]
  -- the scalar compositor on a localized complex
  have hcoh : coh.hom.app (DerivedCategory.Q.obj L₀) ≫ s₀.mapDerivedCategoryFactors.hom.app L₀ =
      s₁.mapDerivedCategory.map (r'.mapDerivedCategoryFactors.hom.app L₀) ≫
        s₁.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map c' := by
    have h₁ := (Iso.eq_inv_comp ((mapDerivedCategoryCompIso r' s₁).app
      (DerivedCategory.Q.obj L₀))).mp (mapDerivedCategoryCompIso_hom_app_factors r' s₁ L₀).symm
    have h₂ := mapDerivedCategoryNatIso_fac c L₀
    simp only [Iso.app_hom] at h₁
    simp only [hcoh_def, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [h₂, reassoc_of% h₁]
  -- the strict square on complexes
  have hstrict : (s₁.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((u₁.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ p') ≫ c' ≫
        (strictSquareComplexIso B₀ P).hom =
      (strictSquareComplexIso B₁ P).hom ≫ (o.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app P) := by
    ext i
    have hi := h (P.X i)
    simp only [Functor.map_comp, Category.assoc] at hi
    simp only [a, p', c', strictSquareComplexIso, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.app_hom, Functor.map_comp,
      Category.assoc, Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
      NatTrans.id_app]
    erw [Functor.map_id, Functor.map_id, Category.id_comp]
    exact hi
  have hnat := coh.hom.naturality (u₀.mapDerivedCategoryFactors.hom.app K₀)
  have hu₁ := u₁.mapDerivedCategoryFactors.hom.naturality a
  have hs₁ := s₁.mapDerivedCategoryFactors.hom.naturality
    ((u₁.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ p')
  have ho := o.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat hu₁ hs₁ ho
  rw [← cancel_mono (o.mapDerivedCategoryFactors.hom.app
    ((τ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))]
  simp only [strictSquareRealization, strictSquareArrow, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, Functor.map_comp]
  rw [ho]
  simp only [Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  have hX : u₁.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
      u₁.mapDerivedCategory.map (r.mapDerivedCategoryFactors.inv.app K₀) ≫
      loc.hom.app (DerivedCategory.Q.obj K₀) ≫
      r'.mapDerivedCategory.map (u₀.mapDerivedCategoryFactors.hom.app K₀) ≫
      r'.mapDerivedCategoryFactors.hom.app L₀ =
      u₁.mapDerivedCategoryFactors.hom.app K₁ ≫
        DerivedCategory.Q.map ((u₁.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ p') := by
    rw [hloc, reassoc_of% hu₁]
    simp only [Functor.map_comp]
  have hX' := congrArg s₁.mapDerivedCategory.map hX
  have hs₁' := hs₁
  have hQ := congrArg DerivedCategory.Q.map hstrict
  simp only [a, Functor.map_comp, Category.assoc] at hX' hs₁' hQ
  erw [Category.comp_id]
  rw [← reassoc_of% hnat, reassoc_of% hcoh, reassoc_of% hX', reassoc_of% hs₁', hQ]

section Transport

variable {𝒜₁ 𝒜₀ ℬ₁ ℬ₀ ℰ : Type*} [Category 𝒜₁] [Category 𝒜₀] [Category ℬ₁] [Category ℬ₀]
  [Category ℰ] {R : 𝒜₀ ⥤ 𝒜₁} {U₁ : 𝒜₁ ⥤ ℬ₁} {U₀ : 𝒜₀ ⥤ ℬ₀} {R' : ℬ₀ ⥤ ℬ₁}
  {S₁ : ℬ₁ ⥤ ℰ} {S₀ : ℬ₀ ⥤ ℰ}

/-- A square of the shape of `strictSquare_localized`, transported along isomorphisms of the
four corners. -/
theorem strictSquare_transport (loc : R ⋙ U₁ ≅ U₀ ⋙ R') (coh : R' ⋙ S₁ ≅ S₀)
    {J₁ K₁ : 𝒜₁} {J₀ K₀ : 𝒜₀} (ε₁ : J₁ ≅ K₁) (ε₀ : J₀ ≅ K₀) (g : K₁ ⟶ R.obj K₀)
    {Z₁ Z₀ T₁ T₀ : ℰ} (Ξ₁ : S₁.obj (U₁.obj K₁) ≅ Z₁) (Ξ₀ : S₀.obj (U₀.obj K₀) ≅ Z₀)
    (z : Z₁ ⟶ Z₀) (ρ₁ : Z₁ ≅ T₁) (ρ₀ : Z₀ ≅ T₀) (t : T₁ ⟶ T₀)
    (hsq : S₁.map (U₁.map g ≫ loc.hom.app K₀) ≫ coh.hom.app (U₀.obj K₀) ≫ Ξ₀.hom = Ξ₁.hom ≫ z)
    (ht : z ≫ ρ₀.hom = ρ₁.hom ≫ t) :
    S₁.map (U₁.map (ε₁.hom ≫ g ≫ R.map ε₀.inv) ≫ loc.hom.app J₀) ≫ coh.hom.app (U₀.obj J₀) ≫
        (S₀.mapIso (U₀.mapIso ε₀) ≪≫ Ξ₀ ≪≫ ρ₀).hom =
      (S₁.mapIso (U₁.mapIso ε₁) ≪≫ Ξ₁ ≪≫ ρ₁).hom ≫ t := by
  have e₁ := loc.hom.naturality ε₀.inv
  have e₂ := coh.hom.naturality (U₀.map ε₀.inv)
  dsimp only [Functor.comp_map, Functor.comp_obj] at e₁ e₂
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc S₁ (U₁.map (R.map ε₀.inv)), e₁, Functor.map_comp_assoc,
    reassoc_of% e₂, ← Functor.map_comp_assoc S₀, ← Functor.map_comp U₀, Iso.inv_hom_id,
    Functor.map_id, Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc] at hsq ⊢
  rw [reassoc_of% hsq, ht]

end Transport

end CategoryTheory.Functor
