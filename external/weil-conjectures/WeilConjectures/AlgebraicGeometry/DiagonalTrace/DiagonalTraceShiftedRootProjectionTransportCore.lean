/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
/-! # Core shifted root-projection transport equation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

private theorem shifted_normalized_unit
    {K D T : Type*} [Category K] [Category D] [Category T]
    [HasShift K ℤ] [HasShift D ℤ] [HasShift T ℤ]
    (Q : K ⥤ D) (U : K ⥤ T) (R₀ R E : D ⥤ T)
    [Q.CommShift ℤ] [U.CommShift ℤ] [R₀.CommShift ℤ] [R.CommShift ℤ]
    (η₀ : U ⟶ Q ⋙ R₀) (η : U ⟶ Q ⋙ R)
    [NatTrans.CommShift η₀ ℤ] [NatTrans.CommShift η ℤ]
    (p₀ : R₀ ⟶ E) (p : R ⟶ E) (X : K) (j : ℤ)
    (h : η₀.app (X⟦j⟧) ≫ p₀.app (Q.obj (X⟦j⟧)) =
      η.app (X⟦j⟧) ≫ p.app (Q.obj (X⟦j⟧))) :
    (η₀.app X)⟦j⟧' ≫ (R₀.commShiftIso j).inv.app (Q.obj X) ≫
        p₀.app ((Q.obj X)⟦j⟧) =
      (η.app X)⟦j⟧' ≫ (R.commShiftIso j).inv.app (Q.obj X) ≫
        p.app ((Q.obj X)⟦j⟧) := by
  rw [NatTrans.shift_app η₀ j X, NatTrans.shift_app η j X]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [p₀.naturality, p.naturality, reassoc_of% h]

private theorem ordinary_shifted_projection_independent
    {B : Type*} [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (L₀ L : DiagonalRlim B) (H : ℕᵒᵖ ⥤ B) (n : ℕ) (j : ℤ) :
    (diagonalOrdinaryRlim L₀ H)⟦j⟧' ≫ (L₀.R.commShiftIso j).inv.app
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        (L₀.projection n).app (((DerivedCategory.singleFunctor _ 0).obj H)⟦j⟧) =
      (diagonalOrdinaryRlim L H)⟦j⟧' ≫ (L.R.commShiftIso j).inv.app
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        (L.projection n).app (((DerivedCategory.singleFunctor _ 0).obj H)⟦j⟧) := by
  let P := (HomologicalComplex.single (ℕᵒᵖ ⥤ B) (.up ℤ) 0).obj H
  simp only [diagonalOrdinaryRlim, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [L₀.R.map_id, L.R.map_id, Category.comp_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  apply shifted_normalized_unit DerivedCategory.Q
    ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    L₀.R L.R _ L₀.η L.η (L₀.projection n) (L.projection n) P j
  apply (cancel_mono
    ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors).hom.app (P⟦j⟧))).1
  simpa only [Category.assoc] using
    (L₀.normalization (P⟦j⟧) n).trans (L.normalization (P⟦j⟧) n).symm

private theorem ordinaryRlim_naturality
    {B : Type*} [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (L : DiagonalRlim B) {H K : ℕᵒᵖ ⥤ B} (f : H ⟶ K) :
    (DerivedCategory.singleFunctor B 0).map ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).map f) ≫
        diagonalOrdinaryRlim L K =
      diagonalOrdinaryRlim L H ≫
        L.R.map ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).map f) := by
  simp only [diagonalOrdinaryRlim, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [L.R.map_id, L.R.map_id, Category.comp_id, Category.comp_id]
  simp only [Category.assoc]
  change DerivedCategory.Q.map
      ((HomologicalComplex.single B (.up ℤ) 0).map (lim.map f)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (lim : (ℕᵒᵖ ⥤ B) ⥤ B) (.up ℤ) 0).inv.app K) ≫ _ =
    DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (lim : (ℕᵒᵖ ⥤ B) ⥤ B) (.up ℤ) 0).inv.app H) ≫
      L.η.app _ ≫ L.R.map (DerivedCategory.Q.map
        ((HomologicalComplex.single (ℕᵒᵖ ⥤ B) (.up ℤ) 0).map f))
  have hn := L.η.naturality
    ((HomologicalComplex.single (ℕᵒᵖ ⥤ B) (.up ℤ) 0).map f)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← DerivedCategory.Q.map_comp_assoc,
    ← DerivedCategory.Q.map_comp_assoc]
  exact congrArg (fun k ↦ DerivedCategory.Q.map k ≫ L.η.app _)
    ((HomologicalComplex.singleMapHomologicalComplex
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B) (.up ℤ) 0).inv.naturality f)

private theorem transport_shifted_cone
    {C D T : Type*} [Category C] [Category D] [Category T]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift T ℤ]
    (W : C ⥤ D) (R E : D ⥤ T) [W.CommShift ℤ] [R.CommShift ℤ]
    (p : R ⟶ E) {X Y : D} {Z : C} {I : T}
    (e : X ⟶ Y) (v : Y ⟶ W.obj Z) (a : I ⟶ R.obj X) (c : I ⟶ R.obj Y)
    (h : a ≫ R.map e = c) (j : ℤ) :
    a⟦j⟧' ≫ (R.commShiftIso j).inv.app X ≫ p.app (X⟦j⟧) ≫
        E.map (e⟦j⟧' ≫ v⟦j⟧' ≫ (W.commShiftIso j).inv.app Z) =
      (c ≫ R.map v)⟦j⟧' ≫ ((W ⋙ R).commShiftIso j).inv.app Z ≫
        p.app (W.obj (Z⟦j⟧)) := by
  simp only [Functor.commShiftIso_comp_inv_app, Functor.map_comp, Category.assoc]
  rw [R.commShiftIso_inv_naturality_assoc v j,
    p.naturality, p.naturality_assoc]
  rw [← p.naturality_assoc (e⟦j⟧'), ← R.commShiftIso_inv_naturality_assoc e j,
    ← (shiftFunctor T j).map_comp_assoc, h]

/--
The post-shift-isomorphism core of generic root-projection transport.  Removing
 the common source shift isomorphism makes this the finite projection transport
 equation itself; the enclosing theorem reinstates that common isomorphism.

Source: diagonal-limit clause (3), normalization of the root-limit comparison;
diagonal trace proof (1), root cone and exact single/shift comparisons.
(blueprint: lem-sfb-diagonal-trace-shifted-root-projection-transport-core).

Proof: expand the normalized shifted single comparison and the strict root
transport, apply the normalized ordinary-limit projection to the single complex,
then use the cone component equation.  Naturality of each shift comparison moves
those arrows through the finite projection; the canonical single comparisons
cancel in the displayed composite.
-/
theorem diagonalTrace_shiftedRootProjection_transport_core
    {A : Type*} {B : Type*} {C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [Abelian B] [Abelian C]
    [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory C]
    (F : A ⥤ B) (V : C ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L₀ L : DiagonalRlim B) (P : A) (N : C)
    (H : ℕᵒᵖ ⥤ B) (J : DerivedCategory (ℕᵒᵖ ⥤ B))
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : F.obj P ≅ limit H) (e : H ≅ V.obj N)
    (π : (Functor.const ℕᵒᵖ).obj (F.obj P) ⟶ V.obj N)
    (hcone : ∀ n : ℕ, t.hom ≫ limit.π H (op n) ≫ e.hom.app (op n) = π.app (op n))
    (n : ℕ) :
    (shiftFunctor (DerivedCategory B) (2 : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
            (DerivedCategory.singleFunctor B 0).map t.hom ≫ diagonalOrdinaryRlim L₀ H) ≫
        (Functor.commShiftIso L₀.R (2 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        L₀.R.map b.inv ≫
        (L₀.projection n).app J ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
          (b ≪≫
            (shiftFunctor (DerivedCategory (ℕᵒᵖ ⥤ B)) (2 : ℤ)).mapIso
              ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).mapIso e) ≪≫
            (shiftFunctor (DerivedCategory (ℕᵒᵖ ⥤ B)) (2 : ℤ)).mapIso
              ((V.mapDerivedCategorySingleFunctor 0).app N).symm ≪≫
            ((Functor.commShiftIso V.mapDerivedCategory (2 : ℤ)).app
              ((DerivedCategory.singleFunctor C 0).obj N)).symm).hom =
      (shiftFunctor (DerivedCategory B) (2 : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
            (DerivedCategory.singleFunctor B 0).map (limit.lift (V.obj N) ⟨F.obj P, π⟩) ≫
            diagonalOrdinaryRlim L (V.obj N) ≫
            L.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N)) ≫
        (Functor.commShiftIso (V.mapDerivedCategory ⋙ L.R) (2 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj N) ≫
        (L.projection n).app
          (V.mapDerivedCategory.obj
            (((DerivedCategory.singleFunctor C 0).obj N)⟦(2 : ℤ)⟧)) := by
  let E := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
  let S := DerivedCategory.singleFunctor B 0
  let T := DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0
  have hlift : t.hom ≫ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).map e.hom =
      limit.lift (V.obj N) ⟨F.obj P, π⟩ := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc]
    change t.hom ≫ limMap e.hom ≫ limit.π (V.obj N) i = _
    rw [limMap_π, limit.lift_π]
    exact hcone i.unop
  have hc : ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
      S.map t.hom ≫ diagonalOrdinaryRlim L H) ≫ L.R.map (T.map e.hom) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        S.map (limit.lift (V.obj N) ⟨F.obj P, π⟩) ≫
        diagonalOrdinaryRlim L (V.obj N) := by
    simp only [Category.assoc]
    rw [← ordinaryRlim_naturality L e.hom, ← S.map_comp_assoc, hlift]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [(L₀.projection n).naturality_assoc]
  rw [← E.map_comp_assoc, b.inv_hom_id, E.map_id, Category.id_comp]
  rw [reassoc_of% (ordinary_shifted_projection_independent L₀ L H n (2 : ℤ))]
  simpa only [S, T, E, Functor.map_comp, Category.assoc] using
    transport_shifted_cone V.mapDerivedCategory L.R E (L.projection n)
    (T.map e.hom) ((V.mapDerivedCategorySingleFunctor 0).inv.app N)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
      S.map t.hom ≫ diagonalOrdinaryRlim L H)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
      S.map (limit.lift (V.obj N) ⟨F.obj P, π⟩) ≫
      diagonalOrdinaryRlim L (V.obj N)) hc 2

end AlgebraicGeometry.ProEtale.DiagonalTrace
