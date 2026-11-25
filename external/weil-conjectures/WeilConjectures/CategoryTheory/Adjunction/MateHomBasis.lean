/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Yoneda

/-!
# Mates of scalar-extension squares on extended objects

Let `T_Y : C_Y ⥤ D_Y` and `T_X : C_X ⥤ D_X` be "extension of scalars along a finite free
extension with basis `b`", in the sense that for all objects `N`, `Z`, the map
`(g_i)_i ↦ ∑ i, b i • T.map (g i)` is a bijection `(Fin d → (N ⟶ Z)) ≃ (T N ⟶ T Z)`.
Given left adjoints `U_Y ⊣ T_Y`, `U_X ⊣ T_X`, additive functors `G_E : C_Y ⥤ C_X`,
`G_F : D_Y ⥤ D_X` with `G_F` commuting with the scalars `b i`, and an isomorphism
`β : T_Y ⋙ G_F ⟶ G_E ⋙ T_X`, the mate `G_F ⋙ U_X ⟶ U_Y ⋙ G_E` of `β` is an isomorphism
at every object of the form `T_Y N`.

The proof is a Yoneda computation: the unit `T_Y N ⟶ T_Y U_Y T_Y N` has basis coordinates
`s_i : N ⟶ U_Y T_Y N` exhibiting `U_Y T_Y N` as the copower `N ^ d`, this copower structure is
equational and hence preserved by `G_E`, and in these coordinates the mate is the identity.
-/

@[expose] public section

set_option autoImplicit false

open Function

namespace CategoryTheory

/-- A finite family `s i : N ⟶ P` such that precomposition `(P ⟶ Z) → (Fin d → (N ⟶ Z))` is
bijective for every `Z` admits retractions `p i` exhibiting `P` as a biproduct of copies
of `N`. -/
theorem exists_biproduct_retractions_of_bijective {C : Type*} [Category C] [Preadditive C]
    {d : ℕ} {N P : C} (s : Fin d → (N ⟶ P))
    (hs : ∀ Z : C, Bijective (fun ψ : P ⟶ Z ↦ fun i ↦ s i ≫ ψ)) :
    ∃ p : Fin d → (P ⟶ N), (∀ i j, s i ≫ p j = if i = j then 𝟙 N else 0) ∧
      ∑ i, p i ≫ s i = 𝟙 P := by
  classical
  choose p hp using fun j : Fin d ↦ (hs N).2 (fun i ↦ if i = j then 𝟙 N else 0)
  refine ⟨p, fun i j ↦ congrFun (hp j) i, (hs P).1 ?_⟩
  funext i
  simp only [Preadditive.comp_sum, ← Category.assoc, Category.comp_id]
  simp only [fun j ↦ congrFun (hp j) i]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj.symm]) (by simp)]
  simp

/-- An equational biproduct structure `s i`, `p i` on `P` makes precomposition with the
inclusions `s i` bijective on all Hom sets out of `P`. -/
theorem bijective_comp_of_biproduct_retractions {C : Type*} [Category C] [Preadditive C]
    {d : ℕ} {N P : C} (s : Fin d → (N ⟶ P)) (p : Fin d → (P ⟶ N))
    (hsp : ∀ i j, s i ≫ p j = if i = j then 𝟙 N else 0) (hps : ∑ i, p i ≫ s i = 𝟙 P)
    (Z : C) : Bijective (fun ψ : P ⟶ Z ↦ fun i ↦ s i ≫ ψ) := by
  classical
  refine ⟨fun ψ ψ' h ↦ ?_, fun g ↦ ⟨∑ j, p j ≫ g j, ?_⟩⟩
  · rw [← Category.id_comp ψ, ← Category.id_comp ψ', ← hps, Preadditive.sum_comp,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Category.assoc, Category.assoc]
    exact congrArg (p i ≫ ·) (congrFun h i)
  · funext i
    simp only [Preadditive.comp_sum, ← Category.assoc, hsp]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj.symm]) (by simp)]
    simp

/-- The mate of an isomorphism between scalar-extension composites is invertible on
scalar-extended objects, provided both scalar extensions satisfy the finite free Hom formula
for the same basis `b`.

Here `TY`, `TX` are the scalar extensions with left adjoints `UY`, `UX` (restriction),
`GE`, `GF` are the horizontal functors, and `β : TY ⋙ GF ⟶ GE ⋙ TX` is the square. -/
theorem isIso_mateEquiv_symm_app_of_homBasis
    {CY CX DY DX : Type*} [Category CY] [Category CX] [Category DY] [Category DX]
    [Preadditive CY] [Preadditive CX] [Preadditive DY] [Preadditive DX]
    {A : Type*} [Semiring A] [Linear A DY] [Linear A DX]
    {TY : CY ⥤ DY} {TX : CX ⥤ DX} {UY : DY ⥤ CY} {UX : DX ⥤ CX}
    (bY : UY ⊣ TY) (bX : UX ⊣ TX) (GE : CY ⥤ CX) [GE.Additive] (GF : DY ⥤ DX) [GF.Additive]
    (β : TY ⋙ GF ⟶ GE ⋙ TX) [IsIso β] {d : ℕ} (b : Fin d → A)
    (hGF : ∀ {K L : DY} (i : Fin d) (h : K ⟶ L), GF.map (b i • h) = b i • GF.map h)
    (hY : ∀ N Z : CY, Bijective (fun g : Fin d → (N ⟶ Z) ↦ ∑ i, b i • TY.map (g i)))
    (hX : ∀ N Z : CX, Bijective (fun g : Fin d → (N ⟶ Z) ↦ ∑ i, b i • TX.map (g i)))
    (N : CY) :
    IsIso (((mateEquiv bY bX).symm (TwoSquare.mk _ _ _ _ β)).app (TY.obj N)) := by
  classical
  let P := UY.obj (TY.obj N)
  obtain ⟨s, hs⟩ := (hY N P).2 (bY.unit.app (TY.obj N))
  have hsY (Z : CY) : Bijective (fun ψ : P ⟶ Z ↦ fun i ↦ s i ≫ ψ) := by
    refine ((hY N Z).of_comp_iff' _).1 ?_
    convert (bY.homEquiv (TY.obj N) Z).bijective using 1
    funext ψ
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, ← hs, Functor.map_comp,
      Preadditive.sum_comp, Linear.smul_comp]
  obtain ⟨p, hsp, hps⟩ := exists_biproduct_retractions_of_bijective s hsY
  have hsX (Z : CX) : Bijective (fun φ : GE.obj P ⟶ Z ↦ fun i ↦ GE.map (s i) ≫ φ) := by
    refine bijective_comp_of_biproduct_retractions _ (fun i ↦ GE.map (p i)) (fun i j ↦ ?_) ?_ Z
    · rw [← GE.map_comp, hsp]
      split_ifs <;> simp
    · simp only [← GE.map_comp, ← GE.map_sum, hps, GE.map_id]
  refine isIso_of_coyoneda_map_bijective _ fun Z ↦ ?_
  let e : (UX.obj (GF.obj (TY.obj N)) ⟶ Z) → (TX.obj (GE.obj N) ⟶ TX.obj Z) :=
    (fun x ↦ inv (β.app N) ≫ x) ∘ bX.homEquiv _ _
  have he : Bijective e :=
    ((isIso_iff_coyoneda_map_bijective (inv (β.app N))).1 inferInstance _).comp
      (bX.homEquiv _ _).bijective
  refine (he.of_comp_iff' _).1 ?_
  refine (congrArg Bijective ?_).mp ((hX (GE.obj N) Z).comp (hsX Z))
  funext φ
  symm
  have key : GF.map (bY.unit.app (TY.obj N)) ≫ β.app P = bX.unit.app (GF.obj (TY.obj N)) ≫
      TX.map (((mateEquiv bY bX).symm (TwoSquare.mk _ _ _ _ β)).app (TY.obj N)) :=
    unit_mateEquiv_symm bY bX (TwoSquare.mk _ _ _ _ β) (TY.obj N)
  simp only [Function.comp_apply, e, Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc (bX.unit.app _), ← key, ← hs, GF.map_sum]
  simp only [hGF, Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp,
    Linear.comp_smul, Category.assoc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hn := β.naturality (s i)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, IsIso.inv_hom_id_assoc]

end CategoryTheory
