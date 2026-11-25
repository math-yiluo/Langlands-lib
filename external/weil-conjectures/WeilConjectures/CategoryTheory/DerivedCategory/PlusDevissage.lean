/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Dévissage for natural transformations on bounded below derived categories

Let `C` and `D` be abelian categories and `τ : F ⟶ G` a natural transformation between
triangulated functors `D⁺(C) ⥤ D⁺(D)`, compatible with the shifts. We show:

- if `τ` is an isomorphism on the objects of `C` satisfying a property `P`, placed in degree `0`,
  then `τ` is an isomorphism on every bounded object all of whose cohomology objects satisfy `P`
  (`DerivedCategory.Plus.isIso_app_of_isGE_of_isLE`). This is the finite-range comparison of
  blueprint `theorem-smooth-base-change-classical-torsion-2`, with the comparison of the two
  hypercohomology spectral sequences replaced by an induction along the truncation triangles;
- if `F` does not lower the cohomological degree, then `Hⁿ(F(τ_{≤ n} X)) ⟶ Hⁿ(F X)` is an
  isomorphism (`DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app`, blueprint
  `theorem-pbc-injective-acyclicity`);
- if both `F` and `G` do not lower the cohomological degree, then the bounded statement extends
  to all bounded below objects (`DerivedCategory.Plus.isIso_app_of_forall_homology`).
-/

@[expose] public section

open CategoryTheory Category Limits Triangulated Pretriangulated

open DerivedCategory.Plus.TStructure (t)

namespace DerivedCategory.Plus

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]

section

variable {F G : Plus C ⥤ Plus D} [F.CommShift ℤ] [G.CommShift ℤ]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- A natural transformation compatible with the shifts is an isomorphism at `X⟦n⟧` if and only
if it is an isomorphism at `X`. -/
lemma isIso_app_shift_iff (X : Plus C) (n : ℤ) : IsIso (τ.app (X⟦n⟧)) ↔ IsIso (τ.app X) := by
  rw [NatTrans.app_shift τ n X]
  constructor
  · intro h
    have : IsIso ((τ.app X)⟦n⟧') := by
      have := IsIso.of_isIso_comp_left ((F.commShiftIso n).hom.app X)
        ((τ.app X)⟦n⟧' ≫ (G.commShiftIso n).inv.app X)
      exact IsIso.of_isIso_comp_right _ ((G.commShiftIso n).inv.app X)
    exact isIso_of_fully_faithful (shiftFunctor (Plus D) n) _
  · intro
    infer_instance

end

variable {F G : Plus C ⥤ Plus D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- An object of `D⁺(C)` concentrated in degree `n` is isomorphic to a single complex. -/
lemma exists_iso_singleFunctor_obj_of_isGE_of_isLE (X : Plus C) (n : ℤ) [X.IsGE n]
    [X.IsLE n] : ∃ (Y : C), Nonempty (X ≅ (singleFunctor C n).obj Y) := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (ι.obj X) n
  exact ⟨Y, ⟨ι.preimageIso (e ≪≫ ((singleFunctorιIso C n).app Y).symm)⟩⟩

omit [F.IsTriangulated] [G.IsTriangulated] in
/-- If `τ` is an isomorphism at an object of `C` placed in degree `0`, then it is an isomorphism at
this object placed in any degree. -/
lemma isIso_app_singleFunctor_obj (Y : C) (h : IsIso (τ.app ((singleFunctor C 0).obj Y)))
    (n : ℤ) : IsIso (τ.app ((singleFunctor C n).obj Y)) := by
  rw [← NatTrans.isIso_app_iff_of_iso τ (((singleFunctors C).shiftIso (-n) n 0 (by lia)).app Y)]
  exact (isIso_app_shift_iff τ _ _).2 h

/-- Blueprint `theorem-smooth-base-change-classical-torsion-2`: if `τ` is an isomorphism on the
objects of `C` satisfying `P`, placed in degree `0`, then it is an isomorphism on every object of
`D⁺(C)` with cohomology concentrated in `[a, a + n - 1]` and satisfying `P` there. -/
lemma isIso_app_of_isGE_of_isLE (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ Y, P Y → IsIso (τ.app ((singleFunctor C 0).obj Y))) (n : ℕ) :
    ∀ (a : ℤ) (X : Plus C), X.IsGE a → X.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj X)) → IsIso (τ.app X) := by
  induction n with
  | zero =>
    intro a X _ _ _
    have : X.IsLE (a - 1) := by simpa using ‹X.IsLE (a + ↑(0 : ℕ) - 1)›
    have hX : IsZero X := t.isZero X (a - 1) a (by lia)
    have hF : IsZero (F.obj X) := F.map_isZero hX
    have hG : IsZero (G.obj X) := G.map_isZero hX
    exact ⟨⟨0, hF.eq_of_src _ _, hG.eq_of_src _ _⟩⟩
  | succ n ih =>
    intro a X _ _ hX
    set b : ℤ := a + n
    have hT := t.triangleLTGE_distinguished b X
    have : X.IsLE b := t.isLE_of_le X (a + ↑(n + 1) - 1) _ (by lia)
    have : ((t.triangleLTGE b).obj X).obj₃.IsLE b :=
      inferInstanceAs (t.IsLE ((t.truncGE b).obj X) b)
    have : ((t.triangleLTGE b).obj X).obj₃.IsGE b :=
      inferInstanceAs (t.IsGE ((t.truncGE b).obj X) b)
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((t.triangleLTGE b).obj X).obj₃ b
    have := isIso_homologyFunctor_map_truncGEπ_app X b b le_rfl
    have hY : P Y := P.prop_of_iso
      (asIso ((homologyFunctor C b).map ((t.truncGEπ b).app X)) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso b).app Y)
      (hX b (by lia) (by lia))
    have h₃ : IsIso (τ.app ((t.triangleLTGE b).obj X).obj₃) := by
      rw [NatTrans.isIso_app_iff_of_iso τ e]
      exact isIso_app_singleFunctor_obj τ Y (hP Y hY) b
    have h₁ : IsIso (τ.app ((t.triangleLTGE b).obj X).obj₁) := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (t.IsGE ((t.truncLT b).obj X) a)
      · exact t.isLE_truncLT_obj _ _ _ (by lia)
      · have := isIso_homologyFunctor_map_truncLTι_app X b q (by lia)
        exact P.prop_of_iso (asIso ((homologyFunctor C q).map ((t.truncLTι b).app X))).symm
          (hX q hq (by lia))
    exact NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ τ hT h₁ h₃

/-- Blueprint `theorem-smooth-base-change-classical-torsion-2`: if `τ` is an isomorphism on the
objects of `C` satisfying `P`, placed in degree `0`, then it is an isomorphism on every bounded
object of `D⁺(C)` all of whose cohomology objects satisfy `P`. -/
lemma isIso_app_of_bounded (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ Y, P Y → IsIso (τ.app ((singleFunctor C 0).obj Y))) (X : Plus C) (a b : ℤ)
    [X.IsGE a] [X.IsLE b] (hX : ∀ q, P ((homologyFunctor C q).obj X)) : IsIso (τ.app X) :=
  have : X.IsLE (a + ↑(b - a + 1).toNat - 1) := t.isLE_of_le X b _ (by lia)
  isIso_app_of_isGE_of_isLE τ P hP (b - a + 1).toNat a X inferInstance this fun q _ _ ↦ hX q

/-- Blueprint `theorem-pbc-injective-acyclicity`: if a triangulated functor
`F : D⁺(C) ⥤ D⁺(D)` does not lower the cohomological degree, then only the cohomology of `X` in
degrees `≤ n` contributes to `Hⁿ(F X)`: the map `Hⁿ(F(τ_{≤ n} X)) ⟶ Hⁿ(F X)` is an isomorphism. -/
lemma isIso_homologyFunctor_map_map_truncLEι_app (F : Plus C ⥤ Plus D) [F.CommShift ℤ]
    [F.IsTriangulated]
    (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (F.obj X)))
    (X : Plus C) (n : ℤ) :
    IsIso ((homologyFunctor D n).map (F.map ((t.truncLEι n).app X))) := by
  have hT := ι.map_distinguished _ (F.map_distinguished _ (t.triangleLTGE_distinguished (n + 1) X))
  exact DerivedCategory.isIso_homologyMap_mor₁ _ hT (n - 1) n (by lia)
    (hF ((t.truncGE (n + 1)).obj X) (n + 1) (n - 1) (by lia))
    (hF ((t.truncGE (n + 1)).obj X) (n + 1) n (by lia))

/-- Blueprint `theorem-smooth-base-change-classical-torsion-2--1` (the formal part): if `F` and `G`
do not lower the cohomological degree and `τ` is an isomorphism on the objects of `C` satisfying
`P`, placed in degree `0`, then `τ` is an isomorphism at every object of `D⁺(C)` all of whose
cohomology objects satisfy `P`. -/
lemma isIso_app_of_forall_homology (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ Y, P Y → IsIso (τ.app ((singleFunctor C 0).obj Y)))
    (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (F.obj X)))
    (hG : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (G.obj X)))
    (X : Plus C) (hX : ∀ q, P ((homologyFunctor C q).obj X)) : IsIso (τ.app X) := by
  obtain ⟨a, ha⟩ := X.2
  have : X.IsGE a := ⟨ha.1⟩
  rw [isIso_iff]
  intro n
  by_cases hn : n < a
  · exact ⟨⟨0, (hF X a n hn).eq_of_src _ _, (hG X a n hn).eq_of_src _ _⟩⟩
  · have h₁ := isIso_homologyFunctor_map_map_truncLEι_app F hF X n
    have h₂ := isIso_homologyFunctor_map_map_truncLEι_app G hG X n
    have h₃ : IsIso (τ.app ((t.truncLE n).obj X)) := by
      have : ((t.truncLE n).obj X).IsLE (a + ↑(n - a + 1).toNat - 1) :=
        t.isLE_of_le _ n _ (by lia)
      refine isIso_app_of_isGE_of_isLE τ P hP (n - a + 1).toNat a _ inferInstance this
        fun q _ hq ↦ ?_
      have := isIso_homologyFunctor_map_truncLTι_app X (n + 1) q (by lia)
      exact P.prop_of_iso (asIso ((homologyFunctor C q).map ((t.truncLTι (n + 1)).app X))).symm
        (hX q)
    have := (homologyFunctor D n).congr_map (τ.naturality ((t.truncLEι n).app X))
    simp only [Functor.map_comp, Functor.id_obj] at this
    have : IsIso ((homologyFunctor D n).map (F.map ((t.truncLEι n).app X)) ≫
        (homologyFunctor D n).map (τ.app X)) := by rw [this]; infer_instance
    exact IsIso.of_isIso_comp_left ((homologyFunctor D n).map (F.map ((t.truncLEι n).app X))) _

end DerivedCategory.Plus
