/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.CategoryTheory.SpectralSequence.Vanishing
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Vanishing of étale cohomology through the Leray spectral sequence

For a morphism of schemes `f : X ⟶ Y` and an abelian étale sheaf `F` on `X`, the Leray spectral
sequence `Hᵖ(Y, Rᵠf_* F) ⟹ Hᵖ⁺ᵠ(X, F)` (the Grothendieck spectral sequence of
`f_*` followed by the global sections on `Y`) shows: if
`Rᵠf_* F = 0` for `q > e` and `Hᵖ(Y, Rᵠf_* F) = 0` for `p > c`, then `Hⁿ(X, F) = 0` for
`n > c + e` (`AlgebraicGeometry.Etale.subsingleton_H_of_rightDerived_lowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/-- Étale cohomology `Hᵠ(X, F)` (as `Ext`-groups) vanishes if and only if the `q`-th right
derived functor of the global sections functor `Γ(X, -)` vanishes at `F`. -/
lemma subsingleton_H_iff_isZero_rightDerived_Γ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H F q) ↔ IsZero ((((Sheaf.sectionsFunctorAt X.smallEtaleTopology
      (⊤_ X.Etale) : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)).rightDerived q).obj F) :=
  Sheaf.subsingleton_H_iff_isZero_rightDerived _ terminalIsTerminal q F

/-- **Leray vanishing.** Let `f : X ⟶ Y` be a morphism of schemes and `F` an abelian étale sheaf
on `X`. If `Rᵠf_* F = 0` for `q > e` and `Hᵖ(Y, Rᵠf_* F) = 0` for every `q` and `p > c`, then
`Hⁿ(X, F) = 0` for `n > c + e`. -/
theorem subsingleton_H_of_rightDerived_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {c e : ℕ}
    (hf : ∀ q : ℕ, e < q →
      IsZero ((((f)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F))
    (hY : ∀ p q : ℕ, c < p →
      Subsingleton (Sheaf.H ((((f)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F) p))
    (n : ℕ) (hn : c + e < n) : Subsingleton (Sheaf.H F n) := by
  rw [subsingleton_H_iff_isZero_rightDerived_Γ]
  have : ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (⊤_ Y.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (⊤_ X.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have hFG := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).isAcyclicComposablePair
    (Sheaf.sectionsFunctorAt Y.smallEtaleTopology (⊤_ Y.Etale) : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)
  refine IsZero.of_iso (Functor.isZero_rightDerived_comp_of_lt_add _ _ hFG F hf
    (fun p q hp ↦ (subsingleton_H_iff_isZero_rightDerived_Γ _ p).1 (hY p q hp)) n hn)
    ((NatIso.rightDerived
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f) n).app F).symm

end AlgebraicGeometry.Etale
