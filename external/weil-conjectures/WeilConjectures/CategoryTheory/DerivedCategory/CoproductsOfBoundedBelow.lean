/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude

/-!
# Commutation with bounded below coproducts from the bounded case

Let `G : D(C) ⥤ D(D)` be a triangulated functor which does not lower degrees (left t-exact).
If `G` commutes with coproducts of uniformly bounded families, then it commutes with coproducts
of uniformly bounded below families (`DerivedCategory.isIso_sigmaComparison_of_isGE`).

Indeed `Hᵐ(G M)` only depends on the truncation `τ_{≤ m} M`: the map `Hᵐ(G(τ_{≤ m} M)) ⟶ Hᵐ(G M)`
is an isomorphism because `G(τ_{> m} M)` lies in degrees `> m`
(`DerivedCategory.isIso_homologyFunctor_map_map_of_isLE`), and the truncations `τ_{≤ m}` of a
family uniformly in degrees `≥ a` are uniformly bounded. This is the way-out argument of
blueprint `corollary-continuity-cohomology--2`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- Let `G` be a triangulated functor which does not lower degrees. If `f : X ⟶ Y` is a morphism
with `X` in degrees `≤ m` which induces isomorphisms on `Hᵏ` for `k ≤ m`, then `G f` induces an
isomorphism on `Hᵐ`: the cone of `f` lies in degrees `> m`, hence so does its image by `G`. -/
lemma isIso_homologyFunctor_map_map_of_isLE (G : DerivedCategory C ⥤ DerivedCategory D)
    [G.CommShift ℤ] [G.IsTriangulated]
    (hG : ∀ (X : DerivedCategory C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    {X Y : DerivedCategory C} (f : X ⟶ Y) (m : ℤ) [X.IsLE m]
    (hf : ∀ k ≤ m, IsIso ((homologyFunctor C k).map f)) :
    IsIso ((homologyFunctor D m).map (G.map f)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hZ : Z.IsGE (m + 1) := by
    rw [isGE_iff]
    intro k hk
    have : IsIso ((homologyFunctor C k).map f) := hf k (by lia)
    refine isZero_homology_obj₃_of_epi_of_mono _ hT k
      (by simpa using (inferInstance : Epi ((homologyFunctor C k).map f))) ?_
    by_cases hk' : k + 1 ≤ m
    · have : IsIso ((homologyFunctor C (k + 1)).map f) := hf (k + 1) hk'
      simpa using (inferInstance : Mono ((homologyFunctor C (k + 1)).map f))
    · exact ⟨fun _ _ _ ↦ (isZero_of_isLE X m (k + 1) (by lia)).eq_of_tgt _ _⟩
  have hGZ := hG Z (m + 1) hZ
  exact isIso_homologyMap_mor₁ _ (G.map_distinguished _ hT) (m - 1) m (by lia)
    (isZero_of_isGE (G.obj Z) (m + 1) _ (by lia) (hX := hGZ))
    (isZero_of_isGE (G.obj Z) (m + 1) _ (by lia) (hX := hGZ))

variable [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {J : Type*} [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C]
  [HasColimitsOfShape (Discrete J) D] [HasExactColimitsOfShape (Discrete J) D]

/-- **Commutation with bounded below coproducts from the bounded case.** Let
`G : D(C) ⥤ D(D)` be a triangulated functor which does not lower degrees. If `G` commutes with
coproducts of families concentrated in a common interval `[a, b]`, then `G` commutes with
coproducts of families concentrated in degrees `≥ a` for a common `a`. -/
theorem isIso_sigmaComparison_of_isGE (G : DerivedCategory C ⥤ DerivedCategory D)
    [G.CommShift ℤ] [G.IsTriangulated]
    (hG₁ : ∀ (X : DerivedCategory C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (hG₂ : ∀ (N : J → DerivedCategory C) (a b : ℤ),
      (∀ j, (N j).IsGE a ∧ (N j).IsLE b) → IsIso (sigmaComparison G N))
    (M : J → DerivedCategory C) (a : ℤ) (hM : ∀ j, (M j).IsGE a) :
    IsIso (sigmaComparison G M) := by
  rw [isIso_iff]
  intro m
  let A (j : J) := (t.truncLE m).obj (M j)
  let fA (j : J) : A j ⟶ M j := (t.truncLEι m).app (M j)
  have hAm (j : J) : (A j).IsLE m := inferInstanceAs (t.IsLE ((t.truncLE m).obj (M j)) m)
  have hfA (j : J) (k : ℤ) (hk : k ≤ m) : IsIso ((homologyFunctor C k).map (fA j)) :=
    isIso_homologyFunctor_map_truncLTι_app _ (m + 1) k (by lia)
  have hA : IsIso (sigmaComparison G A) := by
    refine hG₂ A a m fun j ↦ ⟨?_, hAm j⟩
    have := hM j
    exact inferInstanceAs (t.IsGE ((t.truncLE m).obj (M j)) a)
  have h₁ : IsIso ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fA j))) :=
    isIso_homologyFunctor_map_sigmaMap _ m fun j ↦
      have := hAm j
      isIso_homologyFunctor_map_map_of_isLE G hG₁ _ m (hfA j)
  have h₂ : IsIso ((homologyFunctor D m).map (G.map (Limits.Sigma.map fA))) := by
    have := isLE_sigma _ m hAm
    exact isIso_homologyFunctor_map_map_of_isLE G hG₁ _ m fun k hk ↦
      isIso_homologyFunctor_map_sigmaMap _ k fun j ↦ hfA j k hk
  have := congrArg (homologyFunctor D m).map (sigmaComparison_naturality G fA)
  rw [Functor.map_comp, Functor.map_comp] at this
  have : IsIso ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fA j)) ≫
      (homologyFunctor D m).map (sigmaComparison G M)) := by
    rw [← this]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fA j))) _

end DerivedCategory
