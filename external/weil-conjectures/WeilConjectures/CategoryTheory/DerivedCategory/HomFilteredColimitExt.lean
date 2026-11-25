/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HomFilteredColimit

/-!
# Continuity of `Ext` out of an object of `C` and filtered colimits

Let `C` be an abelian category and `X` an object of `C`. If for every `k : ℕ` the functor
`Ext^k(X, -)` commutes with filtered colimits (elementwise: surjectivity and injectivity of
`colim Ext^k(X, Bᵢ) ⟶ Ext^k(X, B)`), then `X` placed in degree `0` satisfies
`DerivedCategory.HomCommutesWithFilteredColimits`
(`DerivedCategory.HomCommutesWithFilteredColimits.singleFunctor_obj_of_ext`): in negative
degrees the morphisms `X[0] ⟶ B[n]`, `n > 0`, vanish for `t`-structure reasons, and in the other
degrees they are the `Ext` groups.
-/

@[expose] public section

universe w w'

open CategoryTheory Category Limits Abelian

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

namespace HomCommutesWithFilteredColimits

/-- An object `X` of `C` placed in degree `0` satisfies `HomCommutesWithFilteredColimits` if
every `Ext^k(X, -)` commutes with filtered colimits of objects of `C`, spelled out as surjectivity
and injectivity of `colim Ext^k(X, Bᵢ) ⟶ Ext^k(X, B)`. -/
lemma singleFunctor_obj_of_ext [HasExt.{w'} C] (X : C)
    (h : ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (F : I ⥤ C) (c : Cocone F)
      (_ : IsColimit c) (k : ℕ),
      (∀ x : Ext X c.pt k, ∃ (i : I) (y : Ext X (F.obj i) k),
        y.comp (Ext.mk₀ (c.ι.app i)) (add_zero k) = x) ∧
      (∀ (i : I) (y : Ext X (F.obj i) k), y.comp (Ext.mk₀ (c.ι.app i)) (add_zero k) = 0 →
        ∃ (j : I) (t : i ⟶ j), y.comp (Ext.mk₀ (F.map t)) (add_zero k) = 0)) :
    HomCommutesWithFilteredColimits.{w} ((singleFunctor C 0).obj X) := by
  intro I _ _ F c hc n
  by_cases hn : 0 < n
  · have hz (B : C) (f : (singleFunctor C 0).obj X ⟶ (singleFunctor C n).obj B) : f = 0 :=
      TStructure.t.zero f 0 n hn
    refine ⟨fun f ↦ ?_, fun i g _ ↦ ⟨i, 𝟙 i, by rw [hz _ g, zero_comp]⟩⟩
    obtain ⟨i⟩ := IsFiltered.nonempty (C := I)
    exact ⟨i, 0, by rw [hz _ f, zero_comp]⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k := ⟨(-n).toNat, by omega⟩
  let e := (singleFunctors C).shiftIso (k : ℤ) (-k) 0 (by omega)
  let φ (B : C) : Ext X B k ≃ ((singleFunctor C 0).obj X ⟶ (singleFunctor C (-k)).obj B) :=
    Ext.homEquiv.trans ((Iso.refl _).homCongr (e.app B))
  have hφ {B B' : C} (f : B ⟶ B') (y : Ext X B k) :
      φ B' (y.comp (Ext.mk₀ f) (add_zero k)) = φ B y ≫ (singleFunctor C (-k)).map f := by
    simp only [Equiv.trans_apply, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
      ShiftedHom.comp_mk₀, Iso.homCongr_apply, Iso.refl_inv, Iso.app_hom, assoc, id_comp, φ]
    exact congrArg (Ext.homEquiv y ≫ ·) (e.hom.naturality f)
  have hφ₀ (B : C) : φ B 0 = 0 := by
    simp [φ, Ext.zero_hom]
  refine ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩
  · obtain ⟨i, y, hy⟩ := (h I F c hc k).1 ((φ c.pt).symm f)
    refine ⟨i, φ _ y, ?_⟩
    rw [← hφ, hy]
    exact ((φ c.pt).apply_symm_apply f).symm
  · obtain ⟨j, t, ht⟩ := (h I F c hc k).2 i ((φ _).symm g)
      ((φ _).injective (by rw [hφ, Equiv.apply_symm_apply, hg, hφ₀]))
    exact ⟨j, t, by rw [← (φ _).apply_symm_apply g, ← hφ, ht, hφ₀]⟩

end HomCommutesWithFilteredColimits

end DerivedCategory
