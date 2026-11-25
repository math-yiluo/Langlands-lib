/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-!
# Universal arrows for the right derived transport of algebras via free resolutions

Let `RW` be the total right derived functor of `IsoAlgebra.mapOfNatIso e` and let
`d : RW H ⟶ L'` be a morphism such that `u ↦ RW u ≫ d` is bijective on morphisms `I X ⟶ H` out
of free algebras on objects `X` of a shift-stable class `P_C`. Then `u ↦ RW u ≫ d` is bijective
on morphisms `M ⟶ H` for every `M` whose underlying object lies in `P_C`
(`CategoryTheory.Endofunctor.IsoAlgebra.bijective_rightDerivedFunctor_map_comp`): this is the
five lemma for the free resolution triangle `I U M ⟶ I U M ⟶ M ⟶ (I U M)[1]` and its image by
the triangulated functor `RW`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D] [HasDerivedCategory.{v} C]
  [HasDerivedCategory.{v'} D] in
/-- Bijectivity of `u ↦ RW u ≫ d` on morphisms out of `X` is invariant under isomorphisms
`X' ≅ X`. -/
lemma bijective_rightDerivedFunctor_map_comp_of_iso {H : DerivedCategory (IsoAlgebra F)}
    {L' : DerivedCategory (IsoAlgebra G)} (d : (mapOfNatIso e).rightDerivedFunctor.obj H ⟶ L')
    {X X' : DerivedCategory (IsoAlgebra F)} (i : X' ≅ X)
    (h : Function.Bijective (fun u : X ⟶ H ↦ (mapOfNatIso e).rightDerivedFunctor.map u ≫ d)) :
    Function.Bijective (fun u : X' ⟶ H ↦ (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) := by
  have hfun : (fun u : X' ⟶ H ↦ (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) =
      (fun y ↦ (mapOfNatIso e).rightDerivedFunctor.map i.hom ≫ y) ∘
        (fun u : X ⟶ H ↦ (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) ∘
        (fun u ↦ i.inv ≫ u) := by
    ext u
    simp
  rw [hfun]
  refine Function.Bijective.comp ?_ (h.comp ?_)
  · exact ⟨fun y y' hy ↦ (cancel_epi _).1 hy, fun y ↦
      ⟨(mapOfNatIso e).rightDerivedFunctor.map i.inv ≫ y, by simp [← Functor.map_comp_assoc]⟩⟩
  · exact ⟨fun u u' hu ↦ (cancel_epi _).1 hu, fun u ↦ ⟨i.hom ≫ u, by simp⟩⟩

omit [IsGrothendieckAbelian.{v'} D] [HasDerivedCategory.{v'} D] in
/-- **Universal arrows via free resolutions.** If `u ↦ RW u ≫ d` is bijective on morphisms
`I X ⟶ H` for all `X` in a shift-stable class `P_C`, then it is bijective on morphisms `M ⟶ H`
for all `M` whose underlying object lies in `P_C`. -/
theorem bijective_rightDerivedFunctor_map_comp (PC : ObjectProperty (DerivedCategory C))
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    {H : DerivedCategory (IsoAlgebra F)} {L' : DerivedCategory (IsoAlgebra G)}
    (d : (mapOfNatIso e).rightDerivedFunctor.obj H ⟶ L')
    (hfree : ∀ X, PC X → Function.Bijective
      (fun u : (Free.functor F).mapDerivedCategory.obj X ⟶ H ↦
        (mapOfNatIso e).rightDerivedFunctor.map u ≫ d))
    (M : DerivedCategory (IsoAlgebra F)) (hM : PC ((forget F).mapDerivedCategory.obj M)) :
    Function.Bijective (fun u : M ⟶ H ↦ (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) := by
  let RW := (mapOfNatIso e).rightDerivedFunctor
  let I := (Free.functor F).mapDerivedCategory
  let U := (forget F).mapDerivedCategory
  obtain ⟨-, -, -, -, -, -, -, dD, δ, -, -, -, hdist⟩ := exists_freeDerivedWeilResolution F
  let T := Triangle.mk (dD.app M) ((freeWeilDerivedAdjunction F).counit.app M) (δ.app M)
  have hT : T ∈ distTriang _ := hdist M
  let T' := RW.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := RW.map_distinguished T hT
  have hφ0 {X : DerivedCategory (IsoAlgebra F)} : RW.map (0 : X ⟶ H) ≫ d = 0 := by simp
  have hφsub {X : DerivedCategory (IsoAlgebra F)} (u u' : X ⟶ H) :
      RW.map (u - u') ≫ d = RW.map u ≫ d - RW.map u' ≫ d := by
    rw [Functor.map_sub, Preadditive.sub_comp]
  have hφcomp {X X' : DerivedCategory (IsoAlgebra F)} (a : X' ⟶ X) (u : X ⟶ H) :
      RW.map (a ≫ u) ≫ d = RW.map a ≫ RW.map u ≫ d := by
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨hinj₁, hsurj₁⟩ := hfree _ hM
  obtain ⟨hinj₂, hsurj₂⟩ := bijective_rightDerivedFunctor_map_comp_of_iso e d
    ((I.commShiftIso (1 : ℤ)).app (U.obj M)).symm (hfree _ (hPC_shift _ 1 hM))
  constructor
  · intro u u' huu
    rw [← sub_eq_zero]
    have h0 : RW.map (u - u') ≫ d = 0 := by
      rw [hφsub, sub_eq_zero]
      exact huu
    generalize u - u' = w at h0 ⊢
    have h1 : T.mor₂ ≫ w = 0 := hinj₁ (by
      dsimp only
      rw [hφcomp, h0, comp_zero, hφ0])
    obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ T hT w h1
    have h2 : T'.mor₃ ≫ (RW.commShiftIso (1 : ℤ)).inv.app T.obj₁ ≫ RW.map v ≫ d = 0 := by
      have hT'₃ : T'.mor₃ = RW.map T.mor₃ ≫ (RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ := rfl
      rw [hT'₃, Category.assoc, Iso.hom_inv_id_app_assoc, ← hφcomp, ← hv, h0]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT') _ h2
    obtain ⟨w', hw'⟩ := hsurj₂ ((RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ g)
    dsimp only at hw'
    have h3 : RW.map v ≫ d = RW.map (-(T.mor₁⟦(1 : ℤ)⟧' ≫ w')) ≫ d := by
      have hn := RW.commShiftIso_hom_naturality T.mor₁ (1 : ℤ)
      calc RW.map v ≫ d = (RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫
            ((RW.commShiftIso (1 : ℤ)).inv.app T.obj₁ ≫ RW.map v ≫ d) := by
            rw [Iso.hom_inv_id_app_assoc]
        _ = (RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ (T'.rotate.mor₃ ≫ g) := by rw [hg]
        _ = -((RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ (RW.map T.mor₁)⟦(1 : ℤ)⟧' ≫ g) := by
            rw [Triangle.rotate_mor₃, Preadditive.neg_comp, Preadditive.comp_neg]
            rfl
        _ = -(RW.map (T.mor₁⟦(1 : ℤ)⟧') ≫ (RW.commShiftIso (1 : ℤ)).hom.app T.obj₂ ≫ g) := by
            rw [reassoc_of% hn]
        _ = -(RW.map (T.mor₁⟦(1 : ℤ)⟧') ≫ RW.map w' ≫ d) := by
            erw [hw']
            rfl
        _ = RW.map (-(T.mor₁⟦(1 : ℤ)⟧' ≫ w')) ≫ d := by
            rw [Functor.map_neg, Preadditive.neg_comp, hφcomp]
    rw [hv, hinj₂ h3, Preadditive.comp_neg, ← Category.assoc,
      comp_distTriang_mor_zero₃₁ _ hT, zero_comp, neg_zero]
  · intro y
    obtain ⟨x, hx⟩ := hsurj₁ (RW.map T.mor₂ ≫ y)
    dsimp only at hx
    have hx0 : T.mor₁ ≫ x = 0 := hinj₁ (by
      dsimp only
      rw [hφcomp, hx, ← Functor.map_comp_assoc, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero,
        zero_comp, hφ0])
    obtain ⟨u', hu'⟩ := Triangle.yoneda_exact₂ T hT x hx0
    have hy' : T'.mor₂ ≫ (y - (RW.map u' ≫ d : RW.obj M ⟶ L')) = 0 := by
      have hT'₂ : T'.mor₂ = RW.map T.mor₂ := rfl
      rw [hT'₂, Preadditive.comp_sub, ← hx, hu', hφcomp, sub_self]
    obtain ⟨z, hz⟩ := Triangle.yoneda_exact₃ T' hT' _ hy'
    obtain ⟨w, hw⟩ := hsurj₂ ((RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ z)
    dsimp only at hw
    refine ⟨u' + T.mor₃ ≫ w, ?_⟩
    have hT'₃ : T'.mor₃ = RW.map T.mor₃ ≫ (RW.commShiftIso (1 : ℤ)).hom.app T.obj₁ := rfl
    dsimp only
    rw [Functor.map_add, Preadditive.add_comp, hφcomp, hw, ← Category.assoc, ← hT'₃, ← hz,
      add_sub_cancel]

end CategoryTheory.Endofunctor.IsoAlgebra
