/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Commutation with coproducts from the bounded case

Let `G : D(C) ⥤ D(D)` be a triangulated functor and `𝓔` a triangulated subcategory of `D(C)`
stable under the truncations and under coproducts. Suppose that `G` has *finite amplitude on
`𝓔`*: it does not lower degrees, and sends objects of `𝓔` in degrees `≤ b` into degrees
`≤ b + e`. If `G` commutes with coproducts of uniformly bounded families of objects of `𝓔`, then
it commutes with all coproducts of families of objects of `𝓔`
(`DerivedCategory.isIso_sigmaComparison_of_bounded`).

Indeed, `Hᵐ(G M)` only depends on the truncation `τ_{[m - e, m]} M`: the map
`Hᵐ(G(τ_{≤ m} M)) ⟶ Hᵐ(G M)` is an isomorphism because `G(τ_{> m} M)` lies in degrees `> m`, and
`Hᵐ(G(τ_{≤ m} M)) ⟶ Hᵐ(G(τ_{≥ m - e} τ_{≤ m} M))` is an isomorphism because
`G(τ_{< m - e} τ_{≤ m} M)` lies in degrees `< m`. Truncations commute with coproducts, the
cohomology functors commuting with exact coproducts.

This is the formal part of the comparison of blueprint
`corollary-proper-direct-image-finite-coefficients-localizing`, in the form used for the
finite-coefficient localizing categories of blueprint
`proposition-construction-independence-rf-shriek`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in `D(C)`, if `Hᵏ(X₁) ⟶ Hᵏ(X₂)` is
an epimorphism and `Hᵏ⁺¹(X₁) ⟶ Hᵏ⁺¹(X₂)` a monomorphism, then `Hᵏ(X₃) = 0`. -/
lemma isZero_homology_obj₃_of_epi_of_mono (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (k : ℤ) (h₁ : Epi ((homologyFunctor C k).map T.mor₁))
    (h₂ : Mono ((homologyFunctor C (k + 1)).map T.mor₁)) :
    IsZero ((homologyFunctor C k).obj T.obj₃) :=
  (HomologySequence.exact₃ T hT k (k + 1) rfl).isZero_X₂
    ((HomologySequence.epi_homologyMap_mor₁_iff T hT k).1 h₁)
    ((HomologySequence.mono_homologyMap_mor₁_iff T hT k (k + 1) rfl).1 h₂)

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in `D(C)`, if `Hᵏ⁻¹(X₂) ⟶ Hᵏ⁻¹(X₃)`
is an epimorphism and `Hᵏ(X₂) ⟶ Hᵏ(X₃)` a monomorphism, then `Hᵏ(X₁) = 0`. -/
lemma isZero_homology_obj₁_of_epi_of_mono (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (k : ℤ) (h₁ : Epi ((homologyFunctor C (k - 1)).map T.mor₂))
    (h₂ : Mono ((homologyFunctor C k).map T.mor₂)) :
    IsZero ((homologyFunctor C k).obj T.obj₁) := by
  have hδ := (HomologySequence.epi_homologyMap_mor₂_iff T hT (k - 1) k (by lia)).1 h₁
  have hg := (HomologySequence.mono_homologyMap_mor₂_iff T hT k).1 h₂
  have := (HomologySequence.exact₁ T hT (k - 1) k (by lia)).epi_f hg
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (HomologySequence.δ T (k - 1) k (by lia))]
  dsimp at this hδ ⊢
  rw [hδ, zero_comp, comp_zero]

variable [Abelian.HasKInjectiveResolutions C] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C]

/-- A coproduct of objects in degrees `≤ b` lies in degrees `≤ b`. -/
lemma isLE_sigma (X : J → DerivedCategory C) (b : ℤ) (hX : ∀ j, (X j).IsLE b) :
    (∐ X).IsLE b := by
  rw [isLE_iff]
  intro i hi
  have hc := isColimitOfPreserves (homologyFunctor C i) (coproductIsCoproduct X)
  refine (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j ↦ ?_)
  exact (isZero_of_isLE _ b i hi (hX := hX j.as)).eq_of_src _ _

/-- A coproduct of objects in degrees `≥ a` lies in degrees `≥ a`. -/
lemma isGE_sigma (X : J → DerivedCategory C) (a : ℤ) (hX : ∀ j, (X j).IsGE a) :
    (∐ X).IsGE a := by
  rw [isGE_iff]
  intro i hi
  have hc := isColimitOfPreserves (homologyFunctor C i) (coproductIsCoproduct X)
  refine (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j ↦ ?_)
  exact (isZero_of_isGE _ a i hi (hX := hX j.as)).eq_of_src _ _

/-- The cohomology of a coproduct of morphisms is an isomorphism if the cohomology of each
morphism is. -/
lemma isIso_homologyFunctor_map_sigmaMap {X Y : J → DerivedCategory C} (φ : ∀ j, X j ⟶ Y j)
    (k : ℤ) (h : ∀ j, IsIso ((homologyFunctor C k).map (φ j))) :
    IsIso ((homologyFunctor C k).map (Limits.Sigma.map φ)) := by
  have e : (homologyFunctor C k).map (Limits.Sigma.map φ) =
      inv (sigmaComparison (homologyFunctor C k) X) ≫
        Limits.Sigma.map (fun j ↦ (homologyFunctor C k).map (φ j)) ≫
          sigmaComparison (homologyFunctor C k) Y := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp [← Functor.map_comp]
  rw [e]
  infer_instance

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D] [HasColimitsOfShape (Discrete J) D]
  [HasExactColimitsOfShape (Discrete J) D]

omit [HasExactColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) D] in
/-- The comparison maps `∐ G(Xⱼ) ⟶ G(∐ Xⱼ)` are natural in the family `Xⱼ`. -/
@[reassoc]
lemma sigmaComparison_naturality (G : DerivedCategory C ⥤ DerivedCategory D)
    {X Y : J → DerivedCategory C} (φ : ∀ j, X j ⟶ Y j) :
    sigmaComparison G X ≫ G.map (Limits.Sigma.map φ) =
      Limits.Sigma.map (fun j ↦ G.map (φ j)) ≫ sigmaComparison G Y := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  simp [← Functor.map_comp]

/-- **Commutation with coproducts from the bounded case.** Let `G : D(C) ⥤ D(D)` be a
triangulated functor and `𝓔` a triangulated subcategory of `D(C)` stable under the truncations
`τ_{≤ n}`, `τ_{≥ n}` and under coproducts. Suppose that `G` does not lower degrees, and sends
objects of `𝓔` in degrees `≤ b` into degrees `≤ b + e`. If `G` commutes with coproducts of
families of objects of `𝓔` concentrated in a common interval `[a, b]`, then `G` commutes with
coproducts of arbitrary families of objects of `𝓔`. -/
theorem isIso_sigmaComparison_of_bounded (G : DerivedCategory C ⥤ DerivedCategory D)
    [G.CommShift ℤ] [G.IsTriangulated] (𝓔 : ObjectProperty (DerivedCategory C))
    [𝓔.IsTriangulated] [𝓔.IsClosedUnderIsomorphisms]
    (htrunc : ∀ (X : DerivedCategory C) (n : ℤ), 𝓔 X →
      𝓔 ((t.truncLE n).obj X) ∧ 𝓔 ((t.truncGE n).obj X))
    (hsum : ∀ N : J → DerivedCategory C, (∀ j, 𝓔 (N j)) → 𝓔 (∐ N))
    (e : ℤ) (hG₁ : ∀ (X : DerivedCategory C) (b : ℤ), 𝓔 X → X.IsLE b → (G.obj X).IsLE (b + e))
    (hG₂ : ∀ (X : DerivedCategory C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (hG₃ : ∀ (N : J → DerivedCategory C) (a b : ℤ),
      (∀ j, 𝓔 (N j) ∧ (N j).IsGE a ∧ (N j).IsLE b) → IsIso (sigmaComparison G N))
    (M : J → DerivedCategory C) (hM : ∀ j, 𝓔 (M j)) : IsIso (sigmaComparison G M) := by
  rw [isIso_iff]
  intro m
  -- the upper truncation step
  have stepA {X Y : DerivedCategory C} (f : X ⟶ Y) (hX : X.IsLE m)
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
    have hGZ := hG₂ Z (m + 1) hZ
    exact isIso_homologyMap_mor₁ _ (G.map_distinguished _ hT) (m - 1) m (by lia)
      (isZero_of_isGE (G.obj Z) (m + 1) _ (by lia) (hX := hGZ))
      (isZero_of_isGE (G.obj Z) (m + 1) _ (by lia) (hX := hGZ))
  -- the lower truncation step
  have stepB {X Y : DerivedCategory C} (f : X ⟶ Y) (hX : 𝓔 X) (hY : 𝓔 Y)
      (hY' : Y.IsGE (m - e)) (hf : ∀ k, m - e ≤ k → IsIso ((homologyFunctor C k).map f)) :
      IsIso ((homologyFunctor D m).map (G.map f)) := by
    obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle₁ f
    have hW : 𝓔 W := 𝓔.ext_of_isTriangulatedClosed₁ _ hT hX hY
    have hW' : W.IsLE (m - e - 1) := by
      rw [isLE_iff]
      intro k hk
      have : IsIso ((homologyFunctor C k).map f) := hf k (by lia)
      refine isZero_homology_obj₁_of_epi_of_mono _ hT k ?_
        (by simpa using (inferInstance : Mono ((homologyFunctor C k).map f)))
      by_cases hk' : m - e ≤ k - 1
      · have : IsIso ((homologyFunctor C (k - 1)).map f) := hf (k - 1) hk'
        simpa using (inferInstance : Epi ((homologyFunctor C (k - 1)).map f))
      · exact ⟨fun _ _ _ ↦ (isZero_of_isGE Y (m - e) (k - 1) (by lia)).eq_of_src _ _⟩
    have hGW := hG₁ W _ hW hW'
    exact isIso_homologyMap_mor₂ _ (G.map_distinguished _ hT) m (m + 1) rfl
      (isZero_of_isLE (G.obj W) (m - e - 1 + e) _ (by lia) (hX := hGW))
      (isZero_of_isLE (G.obj W) (m - e - 1 + e) _ (by lia) (hX := hGW))
  -- the truncations
  let A (j : J) := (t.truncLE m).obj (M j)
  let fA (j : J) : A j ⟶ M j := (t.truncLEι m).app (M j)
  let T (j : J) := (t.truncGE (m - e)).obj (A j)
  let fB (j : J) : A j ⟶ T j := (t.truncGEπ (m - e)).app (A j)
  have hA (j : J) : 𝓔 (A j) := (htrunc _ m (hM j)).1
  have hT (j : J) : 𝓔 (T j) := (htrunc _ (m - e) (hA j)).2
  have hAm (j : J) : (A j).IsLE m := inferInstanceAs (t.IsLE ((t.truncLE m).obj (M j)) m)
  have hfA (j : J) (k : ℤ) (hk : k ≤ m) : IsIso ((homologyFunctor C k).map (fA j)) :=
    isIso_homologyFunctor_map_truncLTι_app _ (m + 1) k (by lia)
  have hfB (j : J) (k : ℤ) (hk : m - e ≤ k) : IsIso ((homologyFunctor C k).map (fB j)) :=
    isIso_homologyFunctor_map_truncGEπ_app _ (m - e) k hk
  -- the comparison for the bounded family `T`
  have hTb : IsIso (sigmaComparison G T) := by
    refine hG₃ T (m - e) m fun j ↦ ⟨hT j, ?_, ?_⟩
    · exact inferInstanceAs (t.IsGE ((t.truncGE (m - e)).obj (A j)) (m - e))
    · have := hAm j
      exact inferInstanceAs (t.IsLE ((t.truncGE (m - e)).obj (A j)) m)
  -- the squares
  have hsqA := sigmaComparison_naturality G fA
  have hsqB := sigmaComparison_naturality G fB
  have h₁ : IsIso ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fA j))) :=
    isIso_homologyFunctor_map_sigmaMap _ m fun j ↦ stepA _ (hAm j) (hfA j)
  have h₂ : IsIso ((homologyFunctor D m).map (G.map (Limits.Sigma.map fA))) :=
    stepA _ (isLE_sigma _ m hAm) fun k hk ↦ isIso_homologyFunctor_map_sigmaMap _ k
      fun j ↦ hfA j k hk
  have h₃ : IsIso ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fB j))) :=
    isIso_homologyFunctor_map_sigmaMap _ m fun j ↦ stepB _ (hA j) (hT j)
      (inferInstanceAs (t.IsGE ((t.truncGE (m - e)).obj (A j)) (m - e))) (hfB j)
  have h₄ : IsIso ((homologyFunctor D m).map (G.map (Limits.Sigma.map fB))) :=
    stepB _ (hsum _ hA) (hsum _ hT)
      (isGE_sigma _ _ fun j ↦ inferInstanceAs (t.IsGE ((t.truncGE (m - e)).obj (A j)) (m - e)))
      fun k hk ↦ isIso_homologyFunctor_map_sigmaMap _ k fun j ↦ hfB j k hk
  have hAc : IsIso ((homologyFunctor D m).map (sigmaComparison G A)) := by
    have := congrArg (homologyFunctor D m).map hsqB
    rw [Functor.map_comp, Functor.map_comp] at this
    have : IsIso ((homologyFunctor D m).map (sigmaComparison G A) ≫
        (homologyFunctor D m).map (G.map (Limits.Sigma.map fB))) := by
      rw [this]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((homologyFunctor D m).map (G.map (Limits.Sigma.map fB)))
  have := congrArg (homologyFunctor D m).map hsqA
  rw [Functor.map_comp, Functor.map_comp] at this
  have : IsIso ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fA j)) ≫
      (homologyFunctor D m).map (sigmaComparison G M)) := by
    rw [← this]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((homologyFunctor D m).map (Limits.Sigma.map fun j ↦ G.map (fA j))) _

end DerivedCategory
