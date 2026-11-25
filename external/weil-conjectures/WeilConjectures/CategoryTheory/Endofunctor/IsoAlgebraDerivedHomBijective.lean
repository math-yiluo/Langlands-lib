/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit
public import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution

/-!
# Bijectivity of maps out of the derived category of algebras, tested on free objects

Let `F` be an additive autoequivalence of a Grothendieck abelian category `C` and let
`D(IsoAlgebra F)` be the derived category of the algebras `(M, F M ≅ M)`. Every object `K` sits in
the distinguished triangle `Free(For K) ⟶ Free(For K) ⟶ K ⟶ Free(For K)[1]` of
`CategoryTheory.Endofunctor.IsoAlgebra.exists_freeDerivedWeilResolution`. Hence, for a triangulated
functor `L : D(IsoAlgebra F) ⥤ D` and a morphism `ε : L P ⟶ T`, the map
`Hom(K, P) ⟶ Hom(L K, T)`, `g ↦ L g ≫ ε`, is bijective as soon as it is bijective on the shifts of
`Free(For K)`, by the five lemma applied to the long exact sequences of `Hom(-, P)` and
`Hom(L -, T)` (`CategoryTheory.Endofunctor.IsoAlgebra.bijective_map_comp_of_bijective_free`).

Together with `CategoryTheory.Adjunction.bijective_map_comp_free_iff`, this reduces an adjunction
between derived categories of algebras (for instance of Weil sheaves, where the morphisms are not
determined by the underlying morphisms) to bijections between morphisms of underlying objects.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- **Five lemma for `g ↦ L g ≫ ε`.** For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, a
triangulated functor `L` and `ε : L P ⟶ T`, the map `g ↦ L g ≫ ε` on `Hom(X₃, P)` is bijective if
it is injective on `Hom(X₁, P)`, bijective on `Hom(X₂, P)` and `Hom(X₁⟦1⟧, P)`, and surjective on
`Hom(X₂⟦1⟧, P)`. -/
private lemma bijective_map_comp_obj₃ {C D : Type*} [Category C] [Category D] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated] {P : C} {T : D}
    (ε : L.obj P ⟶ T) (Tr : Triangle C) (hTr : Tr ∈ distTriang C)
    (h₁ : Function.Injective fun g : Tr.obj₁ ⟶ P ↦ L.map g ≫ ε)
    (h₂ : Function.Bijective fun g : Tr.obj₂ ⟶ P ↦ L.map g ≫ ε)
    (h₄ : Function.Bijective fun g : Tr.obj₁⟦(1 : ℤ)⟧ ⟶ P ↦ L.map g ≫ ε)
    (h₅ : Function.Surjective fun g : Tr.obj₂⟦(1 : ℤ)⟧ ⟶ P ↦ L.map g ≫ ε) :
    Function.Bijective fun g : Tr.obj₃ ⟶ P ↦ L.map g ≫ ε := by
  have hL : Triangle.mk (L.map Tr.mor₁) (L.map Tr.mor₂)
      (L.map Tr.mor₃ ≫ (L.commShiftIso (1 : ℤ)).hom.app Tr.obj₁) ∈ distTriang D :=
    L.map_distinguished _ hTr
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    have h0 : L.map (g₁ - g₂) ≫ ε = 0 := by
      rw [Functor.map_sub, Preadditive.sub_comp, sub_eq_zero]
      exact hg
    generalize g₁ - g₂ = g at h0 ⊢
    obtain ⟨g', rfl⟩ := Triangle.yoneda_exact₃ _ hTr g (h₂.1 (by simp [h0]))
    have hL' : Triangle.mk (L.map Tr.mor₂)
        (L.map Tr.mor₃ ≫ (L.commShiftIso (1 : ℤ)).hom.app Tr.obj₁)
        (-(L.map Tr.mor₁)⟦(1 : ℤ)⟧') ∈ distTriang D :=
      rot_of_distTriang _ hL
    obtain ⟨k₀, hk₀⟩ := Triangle.yoneda_exact₃ _ hL'
      ((L.commShiftIso (1 : ℤ)).inv.app Tr.obj₁ ≫ L.map g' ≫ ε) (by simpa using h0)
    obtain ⟨k, hk⟩ := h₅ ((L.commShiftIso (1 : ℤ)).hom.app Tr.obj₂ ≫ k₀)
    obtain rfl : g' = -(Tr.mor₁⟦(1 : ℤ)⟧' ≫ k) := h₄.1 (by
      dsimp only at hk ⊢
      rw [← Iso.hom_inv_id_app_assoc (L.commShiftIso (1 : ℤ)) Tr.obj₁ (L.map g' ≫ ε), hk₀,
        Functor.map_neg, Preadditive.neg_comp, Functor.map_comp, Category.assoc, hk,
        L.commShiftIso_hom_naturality_assoc]
      simp)
    rw [Preadditive.comp_neg, ← Category.assoc, comp_distTriang_mor_zero₃₁ _ hTr, zero_comp,
      neg_zero]
  · obtain ⟨x, hx⟩ := h₂.2 (L.map Tr.mor₂ ≫ y)
    dsimp only at hx
    obtain ⟨z, rfl⟩ := Triangle.yoneda_exact₂ _ hTr x (h₁ (by
      dsimp only
      rw [Functor.map_comp, Category.assoc, hx, ← Functor.map_comp_assoc,
        comp_distTriang_mor_zero₁₂ _ hTr]
      simp))
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₃ _ hL (y - L.map z ≫ ε) (by
      rw [Functor.map_comp, Category.assoc] at hx
      simp [Preadditive.comp_sub, ← hx])
    obtain ⟨k, hk⟩ := h₄.2 ((L.commShiftIso (1 : ℤ)).hom.app Tr.obj₁ ≫ w)
    rw [sub_eq_iff_eq_add'] at hw
    refine ⟨z + Tr.mor₃ ≫ k, ?_⟩
    dsimp only at hk ⊢
    rw [Functor.map_add, Preadditive.add_comp, Functor.map_comp, Category.assoc, hk, hw]
    simp

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

/-- **Bijectivity tested on free objects.** For a triangulated functor `L` out of the derived
category of algebras and `ε : L P ⟶ T`, the map `g ↦ L g ≫ ε` on `Hom(K, P)` is bijective if it is
bijective on `Hom(Free(For K)[n], P)` for every `n`. -/
theorem bijective_map_comp_of_bijective_free {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (L : DerivedCategory (IsoAlgebra F) ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    {P : DerivedCategory (IsoAlgebra F)} {T : D} (ε : L.obj P ⟶ T)
    (K : DerivedCategory (IsoAlgebra F))
    (h : ∀ n : ℤ, Function.Bijective fun g : (shiftFunctor _ n).obj
        ((Free.functor F).mapDerivedCategory.obj ((forget F).mapDerivedCategory.obj K)) ⟶ P ↦
          L.map g ≫ ε) :
    Function.Bijective fun g : K ⟶ P ↦ L.map g ≫ ε := by
  obtain ⟨-, -, -, -, -, -, -, dD, δ, -, -, -, hdist⟩ := exists_freeDerivedWeilResolution F
  exact bijective_map_comp_obj₃ L ε _ (hdist K)
    ((Adjunction.bijective_map_comp_iff_of_iso L ε ((shiftFunctorZero _ ℤ).app _)).1 (h 0)).1
    ((Adjunction.bijective_map_comp_iff_of_iso L ε ((shiftFunctorZero _ ℤ).app _)).1 (h 0)) (h 1)
    (h 1).2

end CategoryTheory.Endofunctor.IsoAlgebra
