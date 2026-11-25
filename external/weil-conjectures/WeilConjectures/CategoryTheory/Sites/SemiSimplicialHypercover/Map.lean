/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Basic

/-!
# Images of hypercovers under functors

A cover-preserving functor `F : (C, J) ⥤ (D, K)` between sites with finite limits which
preserves finite limits maps semi-simplicial hypercovers to hypercovers
(`CategoryTheory.SemiSimplicialObject.IsHypercover.map`). The key point is that a compatible
family of faces with values in `U.map F` factors through the image under `F` of the matching
object of `U` (`CategoryTheory.SemiSimplicialObject.exists_comp_map_matchingπ_eq`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {D : Type u'} [Category.{v'} D] [HasFiniteLimits D] (F : C ⥤ D) [PreservesFiniteLimits F]

/-- A compatible family with values in `U.map F` factors through `F` of the matching object of
`U`. -/
lemma exists_comp_map_matchingπ_eq (U : SemiSimplicialObject C) {n : ℕ} {T : D}
    (x : Fin (n + 2) → (T ⟶ F.obj (U.obj n))) (hx : (U.map F).Compatible x) :
    ∃ m : T ⟶ F.obj (U.matching n), ∀ i, m ≫ F.map (U.matchingπ n i) = x i := by
  cases n with
  | zero =>
    refine ⟨Pi.lift x ≫ inv (piComparison F fun _ : Fin 2 ↦ U.obj 0), fun i ↦ ?_⟩
    have h0 : inv (piComparison F fun _ : Fin 2 ↦ U.obj 0) ≫ F.map (Pi.π _ i) = Pi.π _ i := by
      rw [IsIso.inv_comp_eq, piComparison_comp_π]
    exact (Category.assoc _ _ _).trans ((congrArg _ h0).trans (Pi.lift_comp_π x i))
  | succ m =>
    let L := U.matchingLeft m
    let R := U.matchingRight m
    let a : T ⟶ F.obj (∏ᶜ fun _ : Fin (m + 3) ↦ U.obj (m + 1)) :=
      Pi.lift x ≫ inv (piComparison F _)
    have ha (i : Fin (m + 3)) : a ≫ F.map (Pi.π _ i) = x i := by
      have h0 : inv (piComparison F fun _ : Fin (m + 3) ↦ U.obj (m + 1)) ≫ F.map (Pi.π _ i) =
          Pi.π _ i := by
        rw [IsIso.inv_comp_eq, piComparison_comp_π]
      exact (Category.assoc _ _ _).trans ((congrArg _ h0).trans (Pi.lift_comp_π x i))
    have hL (p : MatchingIndex m) : F.map L ≫ F.map (Pi.π _ p) =
        F.map (Pi.π _ p.1.2.succ) ≫ F.map (U.δ m p.1.1) := by
      simp only [← F.map_comp, L, matchingLeft, Pi.lift_comp_π]
    have hR (p : MatchingIndex m) : F.map R ≫ F.map (Pi.π _ p) =
        F.map (Pi.π _ p.1.1.castSucc) ≫ F.map (U.δ m p.1.2) := by
      simp only [← F.map_comp, R, matchingRight, Pi.lift_comp_π]
    have hw : a ≫ F.map L = a ≫ F.map R := by
      rw [← cancel_mono (piComparison F fun _ : MatchingIndex m ↦ U.obj m)]
      refine Pi.hom_ext _ _ fun p ↦ ?_
      simp only [Category.assoc, piComparison_comp_π, hL, hR, reassoc_of% ha]
      exact hx p.1.1 p.1.2 p.2
    refine ⟨equalizer.lift a hw ≫ (PreservesEqualizer.iso F L R).inv, fun i ↦ ?_⟩
    change _ ≫ F.map (equalizer.ι L R ≫ Pi.π _ i) = _
    rw [F.map_comp, Category.assoc, reassoc_of% (PreservesEqualizer.iso_inv_ι F L R),
      equalizer.lift_ι_assoc, ha]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F}

/-- A cover-preserving functor which preserves finite limits maps hypercovers to hypercovers. -/
lemma IsHypercover.map (hF : CoverPreserving J K F) {U : SemiSimplicialObject C}
    (hU : U.IsHypercover J) : (U.map F).IsHypercover K where
  coverSieve_mem T := by
    have hT : IsTerminal (F.obj (⊤_ C)) := terminalIsTerminal.isTerminalObj F _
    refine K.superset_covering ?_ (K.pullback_stable (hT.from T)
      (hF.cover_preserve (hU.coverSieve_mem (⊤_ C))))
    rintro T' g ⟨Z, h, g', ⟨y⟩, -⟩
    exact ⟨g' ≫ F.map y⟩
  liftSieve_mem {n} T x hx := by
    obtain ⟨m, hm⟩ := exists_comp_map_matchingπ_eq F U x hx
    refine K.superset_covering ?_ (K.pullback_stable m
      (hF.cover_preserve (hU.liftSieve_mem _ (U.compatible_matchingπ n))))
    rintro T' g ⟨Z, h, g', ⟨y, hy⟩, hg⟩
    refine ⟨g' ≫ F.map y, fun i ↦ ?_⟩
    change (g' ≫ F.map y) ≫ F.map (U.δ n i) = g ≫ x i
    rw [Category.assoc, ← F.map_comp, hy, F.map_comp, ← Category.assoc, ← hg, Category.assoc,
      hm]

end CategoryTheory.SemiSimplicialObject
