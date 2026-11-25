/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Presentations of derived functors by additive functors

A presentation of a functor `Φ : D(C) ⥤ D(D)` by an additive functor `F : C ⥤ D` is an
isomorphism `Q ⋙ Φ ≅ F.mapHomologicalComplex ⋙ Q`. A natural transformation between
presented functors *represents* an ordinary natural transformation if both agree after
precomposition with `Q`, through the presentations. Representation is stable under
composition, whiskering and the associators, and the isomorphisms
`mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` represent their defining data.
This reduces identities of pasted derived comparisons on images of complexes to identities
of ordinary natural transformations.

Source: Stacks Project, Tag 05RU (universal property of localization) and Tag 05S7.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

/-- A presentation of a functor between derived categories by an additive functor. -/
abbrev DerivedPresentation (Φ : DerivedCategory C ⥤ DerivedCategory D) (F : C ⥤ D)
    [F.Additive] :=
  DerivedCategory.Q ⋙ Φ ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

namespace DerivedPresentation

/-- The canonical presentation of the functor induced by an exact functor. -/
abbrev ofMap (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : DerivedPresentation F.mapDerivedCategory F :=
  F.mapDerivedCategoryFactors

/-- The composite of two presentations. -/
def comp {Φ : DerivedCategory C ⥤ DerivedCategory D} {Ψ : DerivedCategory D ⥤ DerivedCategory
    E}
    {F : C ⥤ D} {G : D ⥤ E} [F.Additive] [G.Additive]
    (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G) :
    DerivedPresentation (Φ ⋙ Ψ) (F ⋙ G) :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight p Ψ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (F.mapHomologicalComplex _) q ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) _) DerivedCategory.Q

omit [HasDerivedCategory C] [HasDerivedCategory D] in
omit [HasDerivedCategory C] [HasDerivedCategory D] in
lemma Q_map_compIso_hom {F : C ⥤ D} {G : D ⥤ E} [F.Additive] [G.Additive]
    (K : CochainComplex C ℤ) :
    DerivedCategory.Q.map ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ := by
  have : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K =
      𝟙 _ := by
    ext i
    rfl
  rw [this]
  exact DerivedCategory.Q.map_id _

lemma comp_hom_app {Φ : DerivedCategory C ⥤ DerivedCategory D}
    {Ψ : DerivedCategory D ⥤ DerivedCategory E}
    {F : C ⥤ D} {G : D ⥤ E} [F.Additive] [G.Additive]
    (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G) (K : CochainComplex C ℤ) :
    (p.comp q).hom.app K = Ψ.map (p.hom.app K) ≫
      q.hom.app ((F.mapHomologicalComplex _).obj K) := by
  simp only [comp, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [Q_map_compIso_hom]
  simp

/-- Transport a presentation along an isomorphism of derived functors. -/
def ofIso {Φ Φ' : DerivedCategory C ⥤ DerivedCategory D} {F : C ⥤ D} [F.Additive]
    (p : DerivedPresentation Φ F) (e : Φ ≅ Φ') : DerivedPresentation Φ' F :=
  isoWhiskerLeft DerivedCategory.Q e.symm ≪≫ p

end DerivedPresentation

open DerivedPresentation

/-- A derived natural transformation represents an ordinary one through presentations. -/
def DerivedRepresents {Φ Ψ : DerivedCategory C ⥤ DerivedCategory D} {F G : C ⥤ D}
    [F.Additive] [G.Additive] (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G)
    (τ : Φ ⟶ Ψ) (τ₀ : F ⟶ G) : Prop :=
  ∀ K : CochainComplex C ℤ, τ.app (DerivedCategory.Q.obj K) ≫ q.hom.app K =
    p.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ₀ (ComplexShape.up ℤ)).app K)

namespace DerivedRepresents

variable {Φ Ψ Ξ : DerivedCategory C ⥤ DerivedCategory D} {F G H : C ⥤ D}
  [F.Additive] [G.Additive] [H.Additive]
  {p : DerivedPresentation Φ F} {q : DerivedPresentation Ψ G} {r : DerivedPresentation Ξ H}

lemma app_eq {τ : Φ ⟶ Ψ} {τ₀ : F ⟶ G} (h : DerivedRepresents p q τ τ₀)
    (K : CochainComplex C ℤ) :
    τ.app (DerivedCategory.Q.obj K) = p.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ₀ (ComplexShape.up ℤ)).app K) ≫ q.inv.app K := by
  rw [← reassoc_of% (h K), Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- Two derived transformations representing the same ordinary transformation agree on
images of complexes. -/
lemma app_eq_app {τ σ : Φ ⟶ Ψ} {τ₀ : F ⟶ G} (h : DerivedRepresents p q τ τ₀)
    (h' : DerivedRepresents p q σ τ₀) (K : CochainComplex C ℤ) :
    τ.app (DerivedCategory.Q.obj K) = σ.app (DerivedCategory.Q.obj K) := by
  rw [h.app_eq, h'.app_eq]

lemma ext' {τ σ : Φ ⟶ Ψ} {τ₀ : F ⟶ G} (h : DerivedRepresents p q τ τ₀)
    (h' : DerivedRepresents p q σ τ₀) : τ = σ :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (app_eq_app h h')

lemma id (p : DerivedPresentation Φ F) : DerivedRepresents p p (𝟙 Φ) (𝟙 F) := by
  intro K
  simp only [NatTrans.id_app, Category.id_comp, NatTrans.mapHomologicalComplex_id]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

lemma comp {τ : Φ ⟶ Ψ} {τ₀ : F ⟶ G} {σ : Ψ ⟶ Ξ} {σ₀ : G ⟶ H}
    (h : DerivedRepresents p q τ τ₀) (h' : DerivedRepresents q r σ σ₀) :
    DerivedRepresents p r (τ ≫ σ) (τ₀ ≫ σ₀) := by
  intro K
  rw [NatTrans.comp_app, Category.assoc, h' K, reassoc_of% (h K),
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Functor.map_comp]

lemma inv {τ : Φ ≅ Ψ} {τ₀ : F ≅ G} (h : DerivedRepresents p q τ.hom τ₀.hom) :
    DerivedRepresents q p τ.inv τ₀.inv := by
  intro K
  have hK := h K
  rw [← cancel_epi (τ.hom.app (DerivedCategory.Q.obj K)), Iso.hom_inv_id_app_assoc,
    reassoc_of% hK, ← Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, Iso.hom_inv_id, NatTrans.mapHomologicalComplex_id,
    NatTrans.id_app, DerivedCategory.Q.map_id, Category.comp_id]

lemma congr {τ τ' : Φ ⟶ Ψ} {τ₀ τ₀' : F ⟶ G} (h : DerivedRepresents p q τ τ₀)
    (e : τ = τ') (e₀ : τ₀ = τ₀') : DerivedRepresents p q τ' τ₀' := by
  subst e e₀
  exact h

end DerivedRepresents

section Basic

open DerivedRepresents

lemma derivedRepresents_mapDerivedCategoryNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    DerivedRepresents (ofMap F) (ofMap G) (mapDerivedCategoryNatIso e).hom e.hom :=
  fun K ↦ mapDerivedCategoryNatIso_fac e K

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
lemma derivedRepresents_mapDerivedCategoryCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedRepresents (ofMap (F ⋙ G)) ((ofMap F).comp (ofMap G))
      (mapDerivedCategoryCompIso F G).inv (𝟙 (F ⋙ G)) := by
  intro K
  have h := mapDerivedCategoryCompIso_fac F G K
  rw [Q_map_compIso_hom] at h
  erw [Category.comp_id] at h
  rw [comp_hom_app, NatTrans.mapHomologicalComplex_id]
  erw [DerivedCategory.Q.map_id, Category.comp_id]
  exact h

lemma derivedRepresents_ofIso {Φ Φ' : DerivedCategory C ⥤ DerivedCategory D} {F : C ⥤ D}
    [F.Additive] (p : DerivedPresentation Φ F) (e : Φ ≅ Φ') :
    DerivedRepresents p (p.ofIso e) e.hom (𝟙 F) := by
  intro K
  simp [DerivedPresentation.ofIso]

lemma DerivedRepresents.whiskerLeft {Ρ : DerivedCategory C ⥤ DerivedCategory D}
    {Φ Ψ : DerivedCategory D ⥤ DerivedCategory E} {R : C ⥤ D} {F G : D ⥤ E}
    [R.Additive] [F.Additive] [G.Additive]
    (r : DerivedPresentation Ρ R) {p : DerivedPresentation Φ F} {q : DerivedPresentation Ψ G}
    {τ : Φ ⟶ Ψ} {τ₀ : F ⟶ G} (h : DerivedRepresents p q τ τ₀) :
    DerivedRepresents (r.comp p) (r.comp q) (Functor.whiskerLeft Ρ τ)
      (Functor.whiskerLeft R τ₀) := by
  intro K
  have hK := h ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hn : Φ.map (r.hom.app K) ≫
      τ.app (DerivedCategory.Q.obj ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      τ.app (Ρ.obj (DerivedCategory.Q.obj K)) ≫ Ψ.map (r.hom.app K) := τ.naturality _
  have he : (NatTrans.mapHomologicalComplex τ₀ (ComplexShape.up ℤ)).app
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (NatTrans.mapHomologicalComplex (Functor.whiskerLeft R τ₀) (ComplexShape.up ℤ)).app K :=
          by
    ext i
    rfl
  rw [comp_hom_app, comp_hom_app, Functor.whiskerLeft_app]
  calc _ = (τ.app (Ρ.obj (DerivedCategory.Q.obj K)) ≫ Ψ.map (r.hom.app K)) ≫
        q.hom.app ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
          (Category.assoc _ _ _).symm
    _ = Φ.map (r.hom.app K) ≫ (τ.app (DerivedCategory.Q.obj
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        q.hom.app ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
          rw [← Category.assoc (Φ.map _), hn]
    _ = Φ.map (r.hom.app K) ≫ (p.hom.app ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft R τ₀)
          (ComplexShape.up ℤ)).app K)) := by
          rw [hK, he]
    _ = _ := (Category.assoc _ _ _).symm

lemma DerivedRepresents.whiskerRight {Φ Ψ : DerivedCategory C ⥤ DerivedCategory D}
    {Ξ : DerivedCategory D ⥤ DerivedCategory E} {F G : C ⥤ D} {X : D ⥤ E}
    [F.Additive] [G.Additive] [X.Additive]
    {p : DerivedPresentation Φ F} {q : DerivedPresentation Ψ G}
    {τ : Φ ⟶ Ψ} {τ₀ : F ⟶ G} (h : DerivedRepresents p q τ τ₀)
    (x : DerivedPresentation Ξ X) :
    DerivedRepresents (p.comp x) (q.comp x) (Functor.whiskerRight τ Ξ)
      (Functor.whiskerRight τ₀ X) := by
  intro K
  have hK := h K
  have hx := x.hom.naturality ((NatTrans.mapHomologicalComplex τ₀ (ComplexShape.up ℤ)).app K)
  have he : (X.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex τ₀ (ComplexShape.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight τ₀ X) (ComplexShape.up ℤ)).app K
          := by
    ext i
    rfl
  rw [comp_hom_app, comp_hom_app, Functor.whiskerRight_app]
  calc _ = Ξ.map (τ.app (DerivedCategory.Q.obj K) ≫ q.hom.app K) ≫
        x.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
          rw [Functor.map_comp, Category.assoc]
    _ = Ξ.map (p.hom.app K) ≫ (Ξ.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex τ₀ (ComplexShape.up ℤ)).app K)) ≫
        x.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
          rw [hK, Functor.map_comp, Category.assoc]
    _ = _ := by
          erw [hx]
          rw [← he, Category.assoc]
          rfl

lemma derivedRepresents_associator {Φ : DerivedCategory C ⥤ DerivedCategory D}
    {Ψ : DerivedCategory D ⥤ DerivedCategory E} {Ξ : DerivedCategory E ⥤ DerivedCategory E'}
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} [F.Additive] [G.Additive] [H.Additive]
    (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G)
    (r : DerivedPresentation Ξ H) :
    DerivedRepresents ((p.comp q).comp r) (p.comp (q.comp r))
      (Functor.associator Φ Ψ Ξ).hom (Functor.associator F G H).hom := by
  intro K
  have h : (NatTrans.mapHomologicalComplex (Functor.associator F G H).hom
      (ComplexShape.up ℤ)).app K = 𝟙 _ := by
    ext i
    rfl
  rw [h]
  erw [DerivedCategory.Q.map_id, Category.comp_id]
  simp only [comp_hom_app, Functor.associator_hom_app, Category.id_comp, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rfl

lemma derivedRepresents_associator_inv {Φ : DerivedCategory C ⥤ DerivedCategory D}
    {Ψ : DerivedCategory D ⥤ DerivedCategory E} {Ξ : DerivedCategory E ⥤ DerivedCategory E'}
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} [F.Additive] [G.Additive] [H.Additive]
    (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G)
    (r : DerivedPresentation Ξ H) :
    DerivedRepresents (p.comp (q.comp r)) ((p.comp q).comp r)
      (Functor.associator Φ Ψ Ξ).inv (Functor.associator F G H).inv :=
  DerivedRepresents.inv (τ := Functor.associator Φ Ψ Ξ) (τ₀ := Functor.associator F G H)
    (derivedRepresents_associator p q r)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
lemma derivedRepresents_mapDerivedCategoryCompIso_inv (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedRepresents ((ofMap F).comp (ofMap G)) (ofMap (F ⋙ G))
      (mapDerivedCategoryCompIso F G).hom (𝟙 (F ⋙ G)) :=
  DerivedRepresents.inv (τ := (mapDerivedCategoryCompIso F G).symm) (τ₀ := Iso.refl (F ⋙ G))
    (derivedRepresents_mapDerivedCategoryCompIso F G)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
lemma derivedRepresents_mapDerivedCategorySquareIso {F₁ : C ⥤ D} {F₂ : D ⥤ E'}
    {G₁ : C ⥤ E} {G₂ : E ⥤ E'}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    DerivedRepresents ((ofMap F₁).comp (ofMap F₂)) ((ofMap G₁).comp (ofMap G₂))
      (mapDerivedCategorySquareIso e).hom e.hom :=
  (((derivedRepresents_mapDerivedCategoryCompIso_inv F₁ F₂).comp
    (derivedRepresents_mapDerivedCategoryNatIso e)).comp
    (derivedRepresents_mapDerivedCategoryCompIso G₁ G₂)).congr
      (by simp [mapDerivedCategorySquareIso]) (by simp)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- A comparison inverse followed by an induced isomorphism. -/
lemma derivedRepresents_mapDerivedCategoryCompIso_symm_trans {F₁ : C ⥤ D} {F₂ : D ⥤ E}
    {G : C ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F₁ ⋙ F₂ ≅ G) :
    DerivedRepresents ((ofMap F₁).comp (ofMap F₂)) (ofMap G)
      (mapDerivedCategoryCompIso F₁ F₂ ≪≫ mapDerivedCategoryNatIso e).hom e.hom :=
  ((derivedRepresents_mapDerivedCategoryCompIso_inv F₁ F₂).comp
    (derivedRepresents_mapDerivedCategoryNatIso e)).congr rfl (by simp)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- An induced isomorphism followed by a comparison. -/
lemma derivedRepresents_mapDerivedCategoryNatIso_trans_compIso {F : C ⥤ E}
    {G₁ : C ⥤ D} {G₂ : D ⥤ E}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F ≅ G₁ ⋙ G₂) :
    DerivedRepresents (ofMap F) ((ofMap G₁).comp (ofMap G₂))
      (mapDerivedCategoryNatIso e ≪≫ (mapDerivedCategoryCompIso G₁ G₂).symm).hom e.hom :=
  ((derivedRepresents_mapDerivedCategoryNatIso e).comp
    (derivedRepresents_mapDerivedCategoryCompIso G₁ G₂)).congr rfl (by simp)

end Basic

end CategoryTheory.Functor
