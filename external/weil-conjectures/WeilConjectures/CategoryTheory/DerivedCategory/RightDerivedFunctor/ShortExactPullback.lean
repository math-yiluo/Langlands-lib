/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Pullback maps of right derived functors along an exact functor

Let `P : C ⥤ C'` be an exact functor between abelian categories, `F : C ⥤ D`, `F' : C' ⥤ D`
additive functors and `α : F ⟶ P ⋙ F'`. Then there is a natural transformation
`RF ⟶ P ⋙ RF'` of right derived functors (`CategoryTheory.Functor.rightDerivedPullback`),
where `P` acts on the derived categories termwise. On a K-injective complex `I` with a
morphism `φ : P(I) ⟶ J` to a K-injective complex `J` it is `α` followed by `F'(φ)`.

For short complexes `S` of functors `C ⥤ D` and `S'` of functors `C' ⥤ D` which are short exact
on injectives and a morphism `S ⟶ S' ∘ P`, the pullback maps of the three terms form a morphism
of triangles from the triangle of right derived functors of `S` to that of `S'` precomposed
with `P` (`CategoryTheory.ShortComplex.rightDerivedTrianglePullback`); in particular they commute
with the connecting maps. Both constructions are compatible with composition of exact functors
(`CategoryTheory.Functor.rightDerivedPullback_comp`,
`CategoryTheory.ShortComplex.rightDerivedTrianglePullback_comp`). This gives the
functoriality of the long exact sequence of cohomology with support in the pair (blueprint
`thm-pur-with-support-exactness`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated DerivedCategory

namespace CategoryTheory

variable {C C' D : Type*} [Category C] [Category C'] [Category D] [Abelian C] [Abelian C']
  [Abelian D] [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']

namespace Functor

section

variable (F : C ⥤ D) [F.Additive]

/-- The unit `Q(F K) ⟶ RF(Q K)` of the right derived functor, for cochain complexes. -/
noncomputable def rightDerivedFunctorUnitQ (K : CochainComplex C ℤ) :
    Q.obj ((F.mapHomologicalComplex _).obj K) ⟶ F.rightDerivedFunctor.obj (Q.obj K) :=
  (quotientCompQhIso D).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
      F.rightDerivedFunctor.map ((quotientCompQhIso C).hom.app K)

@[reassoc]
lemma rightDerivedFunctorUnitQ_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Q.map ((F.mapHomologicalComplex _).map f) ≫ F.rightDerivedFunctorUnitQ L =
      F.rightDerivedFunctorUnitQ K ≫ F.rightDerivedFunctor.map (Q.map f) := by
  have h₁ := (quotientCompQhIso D).inv.naturality ((F.mapHomologicalComplex _).map f)
  have h₂ := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map f)
  have h₃ := (quotientCompQhIso C).hom.naturality f
  dsimp at h₁ h₂ h₃
  simp only [rightDerivedFunctorUnitQ, assoc, ← F.rightDerivedFunctor.map_comp, ← h₃]
  rw [F.rightDerivedFunctor.map_comp, reassoc_of% h₁, reassoc_of% h₂]

lemma rightDerivedFunctorUnitQ_eq (I : CochainComplex C ℤ) [I.IsKInjective] :
    F.rightDerivedFunctorUnitQ I = (F.rightDerivedFunctorObjQIso I).inv := by
  simp [rightDerivedFunctorUnitQ, rightDerivedFunctorObjQIso]

end

variable (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {F : C ⥤ D} {F' : C' ⥤ D} [F.Additive] [F'.Additive]

/-- The natural transformation `F(K) ⟶ RF'(P K)` on the homotopy category used to define the
pullback map of right derived functors. -/
noncomputable def rightDerivedPullbackAux (α : F ⟶ P ⋙ F') :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶
      Qh ⋙ P.mapDerivedCategory ⋙ F'.rightDerivedFunctor :=
  whiskerRight (NatTrans.mapHomotopyCategory α _) Qh ≫
    whiskerRight (mapHomotopyCategoryCompIso (Iso.refl (P ⋙ F')) _).inv Qh ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft _ F'.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight P.mapDerivedCategoryFactorsh.inv _ ≫
    (Functor.associator _ _ _).hom

/-- The pullback map `RF ⟶ P ⋙ RF'` of right derived functors induced by `α : F ⟶ P ⋙ F'`,
where `P` is an exact functor acting termwise on the derived categories. -/
noncomputable def rightDerivedPullback (α : F ⟶ P ⋙ F') :
    F.rightDerivedFunctor ⟶ P.mapDerivedCategory ⋙ F'.rightDerivedFunctor :=
  F.rightDerivedFunctor.rightDerivedDesc F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ (rightDerivedPullbackAux P α)

@[reassoc]
lemma rightDerivedPullback_fac_app (α : F ⟶ P ⋙ F') (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
        (rightDerivedPullback P α).app (Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      Qh.map ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex α _).app K)) ≫
        F'.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((P.mapHomologicalComplex _).obj K)) ≫
        F'.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj K)) := by
  rw [rightDerivedPullback, rightDerived_fac_app]
  have h : (mapHomotopyCategoryCompIso (Iso.refl (P ⋙ F')) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := by
    rw [← cancel_epi ((mapHomotopyCategoryCompIso (Iso.refl (P ⋙ F'))
      (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj K)),
      Iso.hom_inv_id_app, mapHomotopyCategoryCompIso_refl_hom_app, comp_id]
  simp only [rightDerivedPullbackAux, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.mapHomotopyCategory_app,
    h, Functor.map_id, id_comp, comp_id]
  erw [id_comp]
  rfl

/-- The pullback map on cochain complexes: `Q(F K) ⟶ RF(Q K) ⟶ RF'(P(Q K)) ≅ RF'(Q(P K))` is
`α` followed by the unit of `RF'`. -/
@[reassoc]
lemma rightDerivedFunctorUnitQ_rightDerivedPullback_app (α : F ⟶ P ⋙ F')
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K ≫ (rightDerivedPullback P α).app (Q.obj K) ≫
        F'.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app K) =
      Q.map ((NatTrans.mapHomologicalComplex α _).app K) ≫
        F'.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex _).obj K) := by
  have h₁ := (rightDerivedPullback P α).naturality ((quotientCompQhIso C).hom.app K)
  have h₂ : P.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) ≫
      P.mapDerivedCategory.map ((quotientCompQhIso C).hom.app K) ≫
        P.mapDerivedCategoryFactors.hom.app K =
      (quotientCompQhIso C').hom.app ((P.mapHomologicalComplex _).obj K) := by
    rw [← cancel_epi (P.mapDerivedCategoryFactorsh.hom.app _), Iso.hom_inv_id_app_assoc,
      P.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have h₃ := (quotientCompQhIso D).inv.naturality ((NatTrans.mapHomologicalComplex α _).app K)
  dsimp at h₁ h₃
  simp only [rightDerivedFunctorUnitQ, assoc]
  rw [reassoc_of% h₁, rightDerivedPullback_fac_app_assoc, ← reassoc_of% h₃]
  simp only [← Functor.map_comp, h₂]
  rfl

/-- On a K-injective complex `I` with a morphism `φ : P(I) ⟶ J` to a K-injective complex `J`,
the pullback map `RF(I) ⟶ RF'(P I) ⟶ RF'(J)` is `F(I) ⟶ F'(P I) ⟶ F'(J)`. -/
lemma rightDerivedPullback_app_Q_obj (α : F ⟶ P ⋙ F') (I : CochainComplex C ℤ)
    [I.IsKInjective] (J : CochainComplex C' ℤ) [J.IsKInjective]
    (φ : (P.mapHomologicalComplex _).obj I ⟶ J) :
    (rightDerivedPullback P α).app (Q.obj I) ≫
        F'.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app I ≫ Q.map φ) =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        Q.map ((NatTrans.mapHomologicalComplex α _).app I ≫
          (F'.mapHomologicalComplex _).map φ) ≫ (F'.rightDerivedFunctorObjQIso J).inv := by
  rw [← cancel_epi (F.rightDerivedFunctorObjQIso I).inv, Iso.inv_hom_id_assoc,
    ← rightDerivedFunctorUnitQ_eq, ← rightDerivedFunctorUnitQ_eq, Functor.map_comp,
    rightDerivedFunctorUnitQ_rightDerivedPullback_app_assoc, Functor.map_comp, assoc,
    rightDerivedFunctorUnitQ_naturality]

/-- The pullback maps are natural in the functors: a commutative square `τ ≫ α₂ = α₁ ≫ P τ'`
gives a commutative square of right derived functors. -/
lemma rightDerivedFunctorNatTrans_comp_rightDerivedPullback {F₁ F₂ : C ⥤ D} {F'₁ F'₂ : C' ⥤ D}
    [F₁.Additive] [F₂.Additive] [F'₁.Additive] [F'₂.Additive] (τ : F₁ ⟶ F₂) (τ' : F'₁ ⟶ F'₂)
    (α₁ : F₁ ⟶ P ⋙ F'₁) (α₂ : F₂ ⟶ P ⋙ F'₂) (h : τ ≫ α₂ = α₁ ≫ whiskerLeft P τ') :
    rightDerivedFunctorNatTrans τ ≫ rightDerivedPullback P α₂ =
      rightDerivedPullback P α₁ ≫ whiskerLeft P.mapDerivedCategory
        (rightDerivedFunctorNatTrans τ') := by
  refine F₁.rightDerivedFunctor.rightDerived_ext F₁.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext Y
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hK : (NatTrans.mapHomologicalComplex τ _).app K ≫
      (NatTrans.mapHomologicalComplex α₂ _).app K =
      (NatTrans.mapHomologicalComplex α₁ _).app K ≫
        (NatTrans.mapHomologicalComplex τ' _).app ((P.mapHomologicalComplex _).obj K) := by
    ext n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
    exact congr_app h (K.X n)
  have h₁ := (rightDerivedFunctorNatTrans τ').naturality
    (P.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K))
  have h₂ : F'₁.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj ((P.mapHomologicalComplex _).obj K)) ≫
        (rightDerivedFunctorNatTrans τ').app (Qh.obj ((HomotopyCategory.quotient _ _).obj
          ((P.mapHomologicalComplex _).obj K))) =
      Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex τ' _).app ((P.mapHomologicalComplex _).obj K))) ≫
        F'₂.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((P.mapHomologicalComplex _).obj K)) :=
    rightDerivedNatTrans_app _ _ _ _ _ _ _
  have h₃ : F₁.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
        (rightDerivedFunctorNatTrans τ).app (Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      Qh.map ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex τ _).app K)) ≫
        F₂.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) :=
    rightDerivedNatTrans_app _ _ _ _ _ _ _
  dsimp at h₁ ⊢
  rw [reassoc_of% h₃, rightDerivedPullback_fac_app, rightDerivedPullback_fac_app_assoc, h₁]
  erw [reassoc_of% h₂]
  simp only [← Qh.map_comp_assoc, ← Functor.map_comp, hK]

/-- Natural transformations out of a right derived functor are determined by their
compositions with the units `Q(F K) ⟶ RF(Q K)`. -/
lemma rightDerivedFunctor_hom_ext {G : DerivedCategory C ⥤ DerivedCategory D}
    (γ₁ γ₂ : F.rightDerivedFunctor ⟶ G)
    (h : ∀ K, F.rightDerivedFunctorUnitQ K ≫ γ₁.app (Q.obj K) =
      F.rightDerivedFunctorUnitQ K ≫ γ₂.app (Q.obj K)) : γ₁ = γ₂ := by
  refine F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext Y
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have h₁ := γ₁.naturality ((quotientCompQhIso C).hom.app K)
  have h₂ := γ₂.naturality ((quotientCompQhIso C).hom.app K)
  have hK := h K
  simp only [rightDerivedFunctorUnitQ, assoc, h₁, h₂] at hK
  rw [cancel_epi] at hK
  simp only [← assoc] at hK
  simpa using (cancel_mono _).1 hK

@[reassoc]
lemma rightDerivedFunctorUnitQ_rightDerivedPullback_app' (α : F ⟶ P ⋙ F')
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K ≫ (rightDerivedPullback P α).app (Q.obj K) =
      Q.map ((NatTrans.mapHomologicalComplex α _).app K) ≫
        F'.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex _).obj K) ≫
          F'.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.inv.app K) := by
  rw [← rightDerivedFunctorUnitQ_rightDerivedPullback_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [Functor.map_id, comp_id]

section Comp

variable {C'' : Type*} [Category C''] [Abelian C''] [HasDerivedCategory C'']
  [Abelian.HasKInjectiveResolutions C''] (P' : C' ⥤ C'') [P'.Additive]
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P'] (P'' : C ⥤ C'') [P''.Additive]
  [PreservesFiniteLimits P''] [PreservesFiniteColimits P''] [PreservesFiniteLimits (P ⋙ P')]
  [PreservesFiniteColimits (P ⋙ P')] {F'' : C'' ⥤ D} [F''.Additive]

/-- **Compatibility of the pullback maps with composition.** If `P'' ≅ P ⋙ P'` and the maps
`α'' : F ⟶ P'' ⋙ F''`, `α : F ⟶ P ⋙ F'`, `α' : F' ⟶ P' ⋙ F''` are compatible, then the pullback
map along `P''` is the composite of the pullback maps along `P` and `P'`. -/
lemma rightDerivedPullback_comp (ε : P'' ≅ P ⋙ P') (α : F ⟶ P ⋙ F') (α' : F' ⟶ P' ⋙ F'')
    (α'' : F ⟶ P'' ⋙ F'')
    (hα : α'' ≫ Functor.whiskerRight ε.hom F'' = α ≫ Functor.whiskerLeft P α')
    (M : DerivedCategory C) :
    (rightDerivedPullback P'' α'').app M ≫ F''.rightDerivedFunctor.map
        ((mapDerivedCategoryNatIso ε ≪≫ (mapDerivedCategoryCompIso P P').symm).hom.app M) =
      (rightDerivedPullback P α).app M ≫
        (rightDerivedPullback P' α').app (P.mapDerivedCategory.obj M) := by
  have := rightDerivedFunctor_hom_ext
    (rightDerivedPullback P'' α'' ≫ Functor.whiskerRight
      (mapDerivedCategoryNatIso ε ≪≫ (mapDerivedCategoryCompIso P P').symm).hom
        F''.rightDerivedFunctor ≫ (Functor.associator _ _ _).hom)
    (rightDerivedPullback P α ≫ Functor.whiskerLeft P.mapDerivedCategory
      (rightDerivedPullback P' α')) (fun K ↦ by
        have hK : (NatTrans.mapHomologicalComplex α'' _).app K ≫
            (F''.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex ε.hom _).app K) =
            (NatTrans.mapHomologicalComplex α _).app K ≫
              (NatTrans.mapHomologicalComplex α' _).app ((P.mapHomologicalComplex _).obj K) := by
          ext n
          have := congr_app hα (K.X n)
          simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at this
          simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
            Functor.mapHomologicalComplex_map_f]
          exact this
        have h₁ := mapDerivedCategoryNatIso_fac ε K
        have h₂ := mapDerivedCategoryCompIso_fac P P' K
        rw [show (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ P'))
          (ComplexShape.up ℤ)).hom.app K = 𝟙 _ from rfl] at h₂
        erw [Q.map_id, comp_id] at h₂
        have hI : P''.mapDerivedCategoryFactors.inv.app K ≫
            (mapDerivedCategoryNatIso ε).hom.app (Q.obj K) ≫
              (mapDerivedCategoryCompIso P P').inv.app (Q.obj K) =
            Q.map ((NatTrans.mapHomologicalComplex ε.hom _).app K) ≫
              P'.mapDerivedCategoryFactors.inv.app ((P.mapHomologicalComplex _).obj K) ≫
                P'.mapDerivedCategory.map (P.mapDerivedCategoryFactors.inv.app K) := by
          rw [← cancel_epi (P''.mapDerivedCategoryFactors.hom.app K), Iso.hom_inv_id_app_assoc,
            ← reassoc_of% h₁, cancel_epi, ← h₂]
          simp
        have n₁ := (rightDerivedPullback P' α').naturality
          (P.mapDerivedCategoryFactors.inv.app K)
        dsimp at n₁ ⊢
        simp only [comp_id, rightDerivedFunctorUnitQ_rightDerivedPullback_app'_assoc]
        rw [n₁, rightDerivedFunctorUnitQ_rightDerivedPullback_app'_assoc,
          ← F''.rightDerivedFunctor.map_comp (P''.mapDerivedCategoryFactors.inv.app K), hI]
        simp only [Functor.map_comp]
        rw [← rightDerivedFunctorUnitQ_naturality_assoc, ← Q.map_comp_assoc]
        erw [hK]
        simp only [Q.map_comp, assoc]
        rfl)
  have h := congr_app this M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, comp_id,
    Functor.whiskerLeft_app] at h
  exact h

end Comp

end Functor

namespace ShortComplex

variable (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {S : ShortComplex (C ⥤ D)} [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
  {S' : ShortComplex (C' ⥤ D)} [S'.X₁.Additive] [S'.X₂.Additive] [S'.X₃.Additive]
  (hS : S.ShortExactOnInjectives) (hS' : S'.ShortExactOnInjectives)
  (α₁ : S.X₁ ⟶ P ⋙ S'.X₁) (α₂ : S.X₂ ⟶ P ⋙ S'.X₂) (α₃ : S.X₃ ⟶ P ⋙ S'.X₃)
  (h₁₂ : S.f ≫ α₂ = α₁ ≫ Functor.whiskerLeft P S'.f)
  (h₂₃ : S.g ≫ α₃ = α₂ ≫ Functor.whiskerLeft P S'.g)

/-- The morphism of short complexes of cochain complexes `S(I) ⟶ S'(J)` induced by the maps
`α` and a morphism `φ : P(I) ⟶ J`. -/
@[simps]
noncomputable def mapCochainComplexPullback (I : CochainComplex C ℤ) (J : CochainComplex C' ℤ)
    (φ : (P.mapHomologicalComplex _).obj I ⟶ J) :
    S.mapCochainComplex I ⟶ S'.mapCochainComplex J where
  τ₁ := (NatTrans.mapHomologicalComplex α₁ _).app I ≫ (S'.X₁.mapHomologicalComplex _).map φ
  τ₂ := (NatTrans.mapHomologicalComplex α₂ _).app I ≫ (S'.X₂.mapHomologicalComplex _).map φ
  τ₃ := (NatTrans.mapHomologicalComplex α₃ _).app I ≫ (S'.X₃.mapHomologicalComplex _).map φ
  comm₁₂ := by
    ext n
    have := congr_app h₁₂ (I.X n)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at this
    simp only [mapCochainComplex_f,
      HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, assoc]
    erw [S'.f.naturality]
    rw [reassoc_of% this]
    rfl
  comm₂₃ := by
    ext n
    have := congr_app h₂₃ (I.X n)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at this
    simp only [mapCochainComplex_g,
      HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, assoc]
    erw [S'.g.naturality]
    rw [reassoc_of% this]
    rfl

variable [EnoughInjectives C] [EnoughInjectives C']

include α₂ h₁₂ h₂₃ in
/-- The pullback maps commute with the connecting maps of the triangles of right derived
functors of `S` and `S'`. -/
lemma rightDerivedδ_comp_rightDerivedPullback (M : Plus C) :
    (rightDerivedδ hS).app M ≫ ((Functor.rightDerivedPullback P α₁).app M.obj)⟦(1 : ℤ)⟧' =
      (Functor.rightDerivedPullback P α₃).app M.obj ≫
        (rightDerivedδ hS').app (P.mapDerivedCategoryPlus.obj M) := by
  let R := Plus.injectiveModel M
  let R' := Plus.injectiveModel (P.mapDerivedCategoryPlus.obj M)
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKInjective.exists_Q_map_eq
    ((P.mapHomologicalComplex _).obj R.I) R'.I
    (P.mapDerivedCategoryFactors.inv.app R.I ≫ P.mapDerivedCategory.map R.iso.hom ≫ R'.iso.inv)
  have hφ' : P.mapDerivedCategory.map R.iso.hom ≫ R'.iso.inv =
      P.mapDerivedCategoryFactors.hom.app R.I ≫ Q.map φ := by
    rw [hφ, Iso.hom_inv_id_app_assoc]
  have k₁ := Functor.rightDerivedPullback_app_Q_obj P α₁ R.I R'.I φ
  have k₃ := Functor.rightDerivedPullback_app_Q_obj P α₃ R.I R'.I φ
  rw [← hφ'] at k₁ k₃
  have n₁ := (Functor.rightDerivedPullback P α₁).naturality R.iso.hom
  have n₃ := (Functor.rightDerivedPullback P α₃).naturality R.iso.inv
  dsimp at n₁ n₃
  have m₁ : S.X₁.rightDerivedFunctor.map R.iso.hom ≫
      (Functor.rightDerivedPullback P α₁).app M.obj =
      (S.X₁.rightDerivedFunctorObjQIso R.I).hom ≫
        Q.map ((NatTrans.mapHomologicalComplex α₁ _).app R.I ≫
          (S'.X₁.mapHomologicalComplex _).map φ) ≫
        (S'.X₁.rightDerivedFunctorObjQIso R'.I).inv ≫
          S'.X₁.rightDerivedFunctor.map R'.iso.hom := by
    rw [n₁, ← reassoc_of% k₁, ← Functor.map_comp, assoc, Iso.inv_hom_id, comp_id]
  have m₃ : (Functor.rightDerivedPullback P α₃).app M.obj ≫
      S'.X₃.rightDerivedFunctor.map R'.iso.inv =
      S.X₃.rightDerivedFunctor.map R.iso.inv ≫ (S.X₃.rightDerivedFunctorObjQIso R.I).hom ≫
        Q.map ((NatTrans.mapHomologicalComplex α₃ _).app R.I ≫
          (S'.X₃.mapHomologicalComplex _).map φ) ≫
        (S'.X₃.rightDerivedFunctorObjQIso R'.I).inv := by
    rw [← k₃, reassoc_of% n₃, ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      Functor.map_id, id_comp]
  have hδ := triangleOfSESδ_naturality (hS.shortExact_mapCochainComplex R.I)
    (hS'.shortExact_mapCochainComplex R'.I)
    (mapCochainComplexPullback P α₁ α₂ α₃ h₁₂ h₂₃ R.I R'.I φ)
  simp only [mapCochainComplexPullback_τ₁, mapCochainComplexPullback_τ₃] at hδ
  rw [rightDerivedδ_app_eq hS M R, rightDerivedδ_app_eq hS' _ R']
  simp only [rightDerivedδAux, rightDerivedδQObj, assoc]
  rw [reassoc_of% m₃]
  simp only [← Functor.map_comp, m₁, Iso.inv_hom_id_assoc]
  rw [(shiftFunctor _ (1 : ℤ)).map_comp (Q.map _), reassoc_of% hδ]

/-- **Pullback of the triangle of right derived functors.** For an exact functor `P : C ⥤ C'`,
short complexes of functors `S` on `C` and `S'` on `C'` which are short exact on injectives,
and maps `αᵢ : S.Xᵢ ⟶ P ⋙ S'.Xᵢ` commuting with the maps of `S` and `S'`, the pullback maps form
a morphism of triangles `RS(K) ⟶ RS'(P K)`, natural in the bounded below complex `K`. -/
noncomputable def rightDerivedTrianglePullback :
    rightDerivedTriangle hS ⟶ P.mapDerivedCategoryPlus ⋙ rightDerivedTriangle hS' :=
  Triangle.functorHomMk _ _ (Functor.whiskerLeft Plus.ι (Functor.rightDerivedPullback P α₁))
    (Functor.whiskerLeft Plus.ι (Functor.rightDerivedPullback P α₂))
    (Functor.whiskerLeft Plus.ι (Functor.rightDerivedPullback P α₃))
    (by
      ext M
      exact congr_app (Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback P S.f S'.f
        α₁ α₂ h₁₂) M.obj)
    (by
      ext M
      exact congr_app (Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback P S.g S'.g
        α₂ α₃ h₂₃) M.obj)
    (by
      ext M
      exact rightDerivedδ_comp_rightDerivedPullback P hS hS' α₁ α₂ α₃ h₁₂ h₂₃ M)

@[simp]
lemma rightDerivedTrianglePullback_app_hom₁ (M : Plus C) :
    ((rightDerivedTrianglePullback P hS hS' α₁ α₂ α₃ h₁₂ h₂₃).app M).hom₁ =
      (Functor.rightDerivedPullback P α₁).app M.obj := rfl

@[simp]
lemma rightDerivedTrianglePullback_app_hom₂ (M : Plus C) :
    ((rightDerivedTrianglePullback P hS hS' α₁ α₂ α₃ h₁₂ h₂₃).app M).hom₂ =
      (Functor.rightDerivedPullback P α₂).app M.obj := rfl

@[simp]
lemma rightDerivedTrianglePullback_app_hom₃ (M : Plus C) :
    ((rightDerivedTrianglePullback P hS hS' α₁ α₂ α₃ h₁₂ h₂₃).app M).hom₃ =
      (Functor.rightDerivedPullback P α₃).app M.obj := rfl

section Comp

variable {C'' : Type*} [Category C''] [Abelian C''] [HasDerivedCategory C'']
  [Abelian.HasKInjectiveResolutions C''] [EnoughInjectives C''] (P' : C' ⥤ C'') [P'.Additive]
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P'] (P'' : C ⥤ C'') [P''.Additive]
  [PreservesFiniteLimits P''] [PreservesFiniteColimits P''] [PreservesFiniteLimits (P ⋙ P')]
  [PreservesFiniteColimits (P ⋙ P')] (ε : P'' ≅ P ⋙ P')
  {S'' : ShortComplex (C'' ⥤ D)} [S''.X₁.Additive] [S''.X₂.Additive] [S''.X₃.Additive]
  (hS'' : S''.ShortExactOnInjectives)
  (α'₁ : S'.X₁ ⟶ P' ⋙ S''.X₁) (α'₂ : S'.X₂ ⟶ P' ⋙ S''.X₂) (α'₃ : S'.X₃ ⟶ P' ⋙ S''.X₃)
  (h'₁₂ : S'.f ≫ α'₂ = α'₁ ≫ Functor.whiskerLeft P' S''.f)
  (h'₂₃ : S'.g ≫ α'₃ = α'₂ ≫ Functor.whiskerLeft P' S''.g)
  (α''₁ : S.X₁ ⟶ P'' ⋙ S''.X₁) (α''₂ : S.X₂ ⟶ P'' ⋙ S''.X₂) (α''₃ : S.X₃ ⟶ P'' ⋙ S''.X₃)
  (h''₁₂ : S.f ≫ α''₂ = α''₁ ≫ Functor.whiskerLeft P'' S''.f)
  (h''₂₃ : S.g ≫ α''₃ = α''₂ ≫ Functor.whiskerLeft P'' S''.g)

/-- **Compatibility of the pullback of triangles with composition.** If `P'' ≅ P ⋙ P'` and
the maps `α''ᵢ`, `αᵢ`, `α'ᵢ` are compatible, the morphism of triangles along `P''` is the
composite of the morphisms of triangles along `P` and `P'`, up to the comparison
`P''(K) ≅ P'(P(K))`. -/
lemma rightDerivedTrianglePullback_comp
    (hα₁ : α''₁ ≫ Functor.whiskerRight ε.hom S''.X₁ = α₁ ≫ Functor.whiskerLeft P α'₁)
    (hα₂ : α''₂ ≫ Functor.whiskerRight ε.hom S''.X₂ = α₂ ≫ Functor.whiskerLeft P α'₂)
    (hα₃ : α''₃ ≫ Functor.whiskerRight ε.hom S''.X₃ = α₃ ≫ Functor.whiskerLeft P α'₃)
    (M : Plus C) :
    (rightDerivedTrianglePullback P'' hS hS'' α''₁ α''₂ α''₃ h''₁₂ h''₂₃).app M ≫
        (rightDerivedTriangle hS'').map
          ((Functor.mapDerivedCategoryPlusNatIso ε ≪≫
            Functor.mapDerivedCategoryPlusCompIso P P').hom.app M) =
      (rightDerivedTrianglePullback P hS hS' α₁ α₂ α₃ h₁₂ h₂₃).app M ≫
        (rightDerivedTrianglePullback P' hS' hS'' α'₁ α'₂ α'₃ h'₁₂ h'₂₃).app
          (P.mapDerivedCategoryPlus.obj M) := by
  have k₁ := Functor.rightDerivedPullback_comp P P' P'' ε α₁ α'₁ α''₁ hα₁ M.obj
  have k₂ := Functor.rightDerivedPullback_comp P P' P'' ε α₂ α'₂ α''₂ hα₂ M.obj
  have k₃ := Functor.rightDerivedPullback_comp P P' P'' ε α₃ α'₃ α''₃ hα₃ M.obj
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp] at k₁ k₂ k₃
  ext
  · simp only [Pretriangulated.comp_hom₁, rightDerivedTrianglePullback_app_hom₁,
      rightDerivedTriangle,
      Triangle.functorMk_map_hom₁, Functor.comp_map, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    exact k₁
  · simp only [Pretriangulated.comp_hom₂, rightDerivedTrianglePullback_app_hom₂,
      rightDerivedTriangle,
      Triangle.functorMk_map_hom₂, Functor.comp_map, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    exact k₂
  · simp only [Pretriangulated.comp_hom₃, rightDerivedTrianglePullback_app_hom₃,
      rightDerivedTriangle,
      Triangle.functorMk_map_hom₃, Functor.comp_map, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    exact k₃

end Comp

end ShortComplex

end CategoryTheory
