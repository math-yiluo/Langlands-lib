/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.InjectiveHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Morphisms to an injective object are computed on `H⁰`

Let `C` be an abelian category, `I` an injective object of `C` placed in degree `0` and `E` any
object of `D(C)`. Then taking `H⁰` is a bijection

`Hom_{D(C)}(E, I[0]) ≃ Hom_C(H⁰(E), I)`

(`DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective`). Indeed
`Hom(E, I[0]) = Hom(τ_{≤ 0} E, I[0])` since `I[0]` receives no nonzero morphisms from
`D^{≥ 1}`, and `Hom(τ_{≤ 0} E, I[0]) = Hom(H⁰(E)[0], I[0])` since it receives none from `D^{≤ -1}`
either; on the heart `H⁰` is fully faithful.

For `C = Mod_Λ` with `Λ` self-injective this computes the dual `RHom(E, Λ)` degreewise, the
input for degreewise Poincaré duality with coefficients `ℤ/ℓᵐ`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

open TStructure (t)

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₁ ∈ D^{≤ -1}`, precomposition with
`X₂ ⟶ X₃` is a bijection `Hom(X₃, Y) ≃ Hom(X₂, Y)` for every `Y ∈ D^{≥ 0}`. -/
lemma bijective_comp_mor₂_of_isLE_of_isGE (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) [T.obj₁.IsLE (-1)] (Y : DerivedCategory C) [Y.IsGE 0] :
    Function.Bijective (fun h : T.obj₃ ⟶ Y ↦ T.mor₂ ≫ h) := by
  have : (T.obj₁⟦(1 : ℤ)⟧).IsLE (-2) := t.isLE_shift T.obj₁ (-1) 1 (-2) (by omega)
  refine ⟨fun h₁ h₂ hh ↦ ?_, fun g ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ hT (h₁ - h₂)
      (by simpa [Preadditive.comp_sub, sub_eq_zero] using hh)
    rw [hk, t.zero k (-2) 0, comp_zero]
  · obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ hT g (t.zero _ (-1) 0)
    exact ⟨h, hh.symm⟩

/-- **Morphisms to an injective object are computed on `H⁰`.** For `I` injective in `C` and
`E ∈ D(C)`, taking `H⁰` is a bijection `Hom(E, I[0]) ≃ Hom(H⁰(E), H⁰(I[0]))`. -/
theorem bijective_homologyFunctor_map_singleFunctor_of_injective (E : DerivedCategory C)
    (I : C) [Injective I] :
    Function.Bijective (fun f : E ⟶ (singleFunctor C 0).obj I ↦ (homologyFunctor C 0).map f) := by
  -- `K = τ_{< 1} E` and `P = τ_{≥ 0} K`
  let K := (t.truncLT 1).obj E
  let ι : K ⟶ E := (t.truncLTι 1).app E
  let P := (t.truncGE 0).obj K
  let π : K ⟶ P := (t.truncGEπ 0).app K
  have : t.IsLE K 0 := t.isLE_truncLT_obj E 1 0
  have : P.IsLE 0 := inferInstanceAs (t.IsLE ((t.truncGE 0).obj K) 0)
  have : P.IsGE 0 := inferInstanceAs (t.IsGE ((t.truncGE 0).obj K) 0)
  have : ((t.triangleLTGE 1).obj E).obj₃.IsGE 1 :=
    inferInstanceAs (t.IsGE ((t.truncGE 1).obj E) 1)
  have hι := bijective_comp_singleFunctor_of_injective_of_isGE _
    (t.triangleLTGE_distinguished 1 E) I
  have : ((t.triangleLTGE 0).obj K).obj₁.IsLE (-1) :=
    t.isLE_truncLT_obj K 0 (-1)
  have hπ := bijective_comp_mor₂_of_isLE_of_isGE _ (t.triangleLTGE_distinguished 0 K)
    ((singleFunctor C 0).obj I)
  have hP := homologyFunctor_map_bijective_of_isGE_of_isLE (P := P)
    (Q := (singleFunctor C 0).obj I) 0
  have : IsIso ((homologyFunctor C 0).map ι) :=
    isIso_homologyFunctor_map_truncLTι_app E 1 0 (by omega)
  have : IsIso ((homologyFunctor C 0).map π) :=
    isIso_homologyFunctor_map_truncGEπ_app K 0 0 le_rfl
  refine ⟨fun f₁ f₂ hf ↦ hι.1 ?_, fun φ ↦ ?_⟩
  · -- injectivity: `ι ≫ f` is determined by its `H⁰`
    obtain ⟨h₁, hh₁⟩ := hπ.2 (ι ≫ f₁)
    obtain ⟨h₂, hh₂⟩ := hπ.2 (ι ≫ f₂)
    simp only at hh₁ hh₂ hf ⊢
    have hh : h₁ = h₂ := hP.1 (by
      simp only
      rw [← cancel_epi ((homologyFunctor C 0).map π), ← Functor.map_comp, ← Functor.map_comp]
      erw [hh₁, hh₂]
      rw [Functor.map_comp, Functor.map_comp, hf])
    erw [← hh₁, ← hh₂, hh]
  · -- surjectivity
    obtain ⟨h, hh⟩ := hP.2 (inv ((homologyFunctor C 0).map π) ≫
      (homologyFunctor C 0).map ι ≫ φ)
    obtain ⟨f, hf⟩ := hι.2 (π ≫ h)
    refine ⟨f, ?_⟩
    simp only at hh hf ⊢
    rw [← cancel_epi ((homologyFunctor C 0).map ι), ← Functor.map_comp]
    erw [hf]
    rw [Functor.map_comp, hh, IsIso.hom_inv_id_assoc]

end DerivedCategory
