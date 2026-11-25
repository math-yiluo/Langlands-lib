/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Vanishing of morphisms into shifts of bounded objects

Let `C` be an abelian category, `U : C` and `P` a property of objects of `C` such that
`Hom_{D(C)}(U, Y[m]) = 0` for all `Y` satisfying `P` and all `m ≥ d`. Then for every bounded
object `M` of `D(C)` with homology objects satisfying `P` and concentrated in degrees `≤ b`,
`Hom_{D(C)}(U, M[m]) = 0` for all `m ≥ b + d`. This is the formal part of the statement that a
bound on the cohomological dimension of a functor on objects gives a bound on its
hypercohomology on bounded complexes, and is proved by induction on the amplitude of `M` using
the truncation triangles of the canonical t-structure.

## Main statements

- `DerivedCategory.subsingleton_shiftedHom_of_isGE_of_isLE`: the vanishing statement above.
- `DerivedCategory.subsingleton_shiftedHom_of_ext`: the same statement, with the hypothesis on
  `P` phrased with `Ext`-groups.
- `DerivedCategory.Plus.singleFunctorHomEquivExt`: morphisms `X[0] ⟶ Y[0][n]` in the bounded
  below derived category `DerivedCategory.Plus C` are the `Ext`-groups `Ext^n(X, Y)`.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Morphisms from a fixed object into the middle term of a distinguished triangle, shifted
by `m`, vanish as soon as they vanish into the outer terms, shifted by `m`. -/
lemma subsingleton_shiftedHom_obj₂ {U : DerivedCategory C} (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (m : ℤ) (h₁ : Subsingleton (ShiftedHom U T.obj₁ m))
    (h₃ : Subsingleton (ShiftedHom U T.obj₃ m)) : Subsingleton (ShiftedHom U T.obj₂ m) := by
  refine subsingleton_of_forall_eq 0 fun f ↦ ?_
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (Triangle.shift_distinguished T hT m) f
    (h₃.elim _ _)
  rw [hg, h₁.elim g 0, zero_comp]

/-- Let `U : C` and `P` a property of objects of `C`, closed under isomorphisms, such that
`Hom(U, Y[m]) = 0` in `D(C)` for every `Y` satisfying `P` and every `m ≥ d`. Let `M` be an
object of `D(C)` with homology concentrated in `[a, a + n - 1]`, all of whose homology objects
in that range satisfy `P`. Then `Hom(U, M[m]) = 0` for `m ≥ a + n - 1 + d`: by induction on `n`,
using the truncation triangle `τ_{< b} M ⟶ M ⟶ τ_{≥ b} M ⟶` with `b = a + n - 1`, whose third
term is `H^b M` placed in degree `b`. -/
lemma subsingleton_shiftedHom_of_isGE_of_isLE_aux (U : C) (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (d : ℤ)
    (hP : ∀ Y, P Y → ∀ m : ℤ, d ≤ m →
      Subsingleton (ShiftedHom ((singleFunctor C 0).obj U) ((singleFunctor C 0).obj Y) m))
    (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj M)) →
      ∀ m : ℤ, a + n - 1 + d ≤ m → Subsingleton (ShiftedHom ((singleFunctor C 0).obj U) M m) := by
  induction n with
  | zero =>
    intro a M _ _ _ m _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    have hM : IsZero M := TStructure.t.isZero M (a - 1) a (by lia)
    exact ⟨fun f g ↦ ((shiftFunctor _ m).map_isZero hM).eq_of_tgt f g⟩
  | succ n ih =>
    intro a M _ _ hM m hm
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    -- the third term is `H^b M` placed in degree `b`
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor C (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor C b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀ h₁
    have hY : P Y := P.prop_of_iso
      (asIso ((homologyFunctor C b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app Y)
      (hM b (by lia) (by lia))
    have h₃ : Subsingleton (ShiftedHom ((singleFunctor C 0).obj U)
        ((TStructure.t.triangleLTGE b).obj M).obj₃ m) := by
      have := hP Y hY (m - b) (by lia)
      let e' : (((TStructure.t.triangleLTGE b).obj M).obj₃)⟦m⟧ ≅
          ((singleFunctor C 0).obj Y)⟦m - b⟧ :=
        (shiftFunctor _ m).mapIso
          (e ≪≫ (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app Y).symm) ≪≫
          ((shiftFunctorAdd' (DerivedCategory C) (-b) m (m - b) (by lia)).app _).symm
      exact ((Iso.refl _).homCongr e').subsingleton
    -- the first term is handled by induction
    have h₁ : Subsingleton (ShiftedHom ((singleFunctor C 0).obj U)
        ((TStructure.t.triangleLTGE b).obj M).obj₁ m) := by
      refine ih a _ ?_ ?_ (fun q hq hq' ↦ ?_) m (by lia)
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact P.prop_of_iso
          (asIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm
          (hM q hq (by lia))
    exact subsingleton_shiftedHom_obj₂ _ hT m h₁ h₃

/-- **Vanishing of morphisms into shifts of bounded objects.** Let `U : C` and `P` a property
of objects of `C`, closed under isomorphisms, such that `Hom(U, Y[m]) = 0` in `D(C)` for every
`Y` satisfying `P` and every `m ≥ d`. Let `M` be an object of `D(C)` with homology concentrated
in `[a, b]`, all of whose homology objects in degrees `≤ b` satisfy `P`. Then `Hom(U, M[m]) = 0`
for all `m ≥ b + d`. -/
lemma subsingleton_shiftedHom_of_isGE_of_isLE (U : C) (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (d : ℤ)
    (hP : ∀ Y, P Y → ∀ m : ℤ, d ≤ m →
      Subsingleton (ShiftedHom ((singleFunctor C 0).obj U) ((singleFunctor C 0).obj Y) m))
    (M : DerivedCategory C) (a b : ℤ) [M.IsGE a] [M.IsLE b]
    (hM : ∀ q, q ≤ b → P ((homologyFunctor C q).obj M)) (m : ℤ) (hm : b + d ≤ m) :
    Subsingleton (ShiftedHom ((singleFunctor C 0).obj U) M m) := by
  by_cases hab : a ≤ b
  · have : M.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le M b _ (by lia)
    exact subsingleton_shiftedHom_of_isGE_of_isLE_aux U P d hP (b - a + 1).toNat a M
      inferInstance this (fun q _ hq ↦ hM q (by lia)) m (by lia)
  · have hM : IsZero M := TStructure.t.isZero M b a (by lia)
    exact ⟨fun f g ↦ ((shiftFunctor _ m).map_isZero hM).eq_of_tgt f g⟩

/-- A version of `DerivedCategory.subsingleton_shiftedHom_of_isGE_of_isLE` where the
hypothesis on `P` is phrased with `Ext`-groups: if `Ext^m(U, Y) = 0` for every `Y` satisfying
`P` and every `m ≥ d`, then `Hom(U, M[m]) = 0` in `D(C)` for every `M` with homology
concentrated in `[a, b]` and satisfying `P`, and every `m ≥ b + d`. -/
lemma subsingleton_shiftedHom_of_ext [HasExt.{w'} C] (U : C) (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (d : ℕ)
    (hP : ∀ Y, P Y → ∀ m : ℕ, d ≤ m → Subsingleton (Abelian.Ext.{w'} U Y m))
    (M : DerivedCategory C) (a b : ℤ) [M.IsGE a] [M.IsLE b]
    (hM : ∀ q, q ≤ b → P ((homologyFunctor C q).obj M)) (m : ℤ) (hm : b + d ≤ m) :
    Subsingleton (ShiftedHom ((singleFunctor C 0).obj U) M m) := by
  refine subsingleton_shiftedHom_of_isGE_of_isLE U P d (fun Y hY m hm ↦ ?_) M a b hM m hm
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by lia)
  have := hP Y hY m (by lia)
  exact Abelian.Ext.homEquiv.{w}.symm.subsingleton

end DerivedCategory

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

/-- Morphisms `X[0] ⟶ Y[0][n]` in the bounded below derived category are the elements of
`Ext^n(X, Y)`. -/
noncomputable def singleFunctorHomEquivExt (X Y : C) (n : ℕ) :
    ((singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) ≃
      Abelian.Ext.{w'} X Y n :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans
    ((Iso.homCongr (Iso.refl _) ((Plus.ι.commShiftIso (n : ℤ)).app _)).trans
      Abelian.Ext.homEquiv.symm)

/-- Precomposing a morphism `X[0] ⟶ Y[0][n]` with the image of `a : X' ⟶ X` corresponds to
composing the `Ext`-class with `a`. -/
lemma singleFunctorHomEquivExt_singleFunctor_map_comp {X X' Y : C} (a : X' ⟶ X) {n : ℕ}
    (t : (singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    singleFunctorHomEquivExt X' Y n ((singleFunctor C 0).map a ≫ t) =
      (Abelian.Ext.mk₀ a).comp (singleFunctorHomEquivExt X Y n t) (zero_add n) := by
  ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  have e₁ (Z : C) (t' : (singleFunctor C 0).obj Z ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
      (singleFunctorHomEquivExt Z Y n t').hom =
        Plus.ι.map t' ≫ ((Plus.ι.commShiftIso (n : ℤ)).app ((singleFunctor C 0).obj Y)).hom := by
    refine (Abelian.Ext.homEquiv.apply_symm_apply _).trans ?_
    exact Category.id_comp _
  rw [e₁, e₁, Functor.map_comp, Category.assoc]
  rfl

@[simp]
lemma singleFunctorHomEquivExt_zero (X Y : C) (n : ℕ) :
    singleFunctorHomEquivExt X Y n 0 = 0 := by
  have := singleFunctorHomEquivExt_singleFunctor_map_comp (0 : X ⟶ X)
    (0 : (singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧)
  rwa [Functor.map_zero, Limits.zero_comp, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp] at this

end DerivedCategory.Plus
