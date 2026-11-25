/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The dual formula for an exceptional inverse image, formally

Let `P ⊣ S` be an adjunction between braided monoidal categories, playing the role of
`Rf_! ⊣ Rf^!` for a morphism `f : X ⟶ Y`, and let `π_K : P K ⊗ M ⟶ P (K ⊗ M')` be a family of
morphisms natural in `K`, playing the role of the projection morphism
`Rf_! K ⊗ᴸ M ⟶ Rf_!(K ⊗ᴸ Lf^* M)`. This file proves the formal part of the dual formula
`Rf^! L ≅ 𝔻_X(f^* 𝔻_Y L)`: if `L ≅ RHom(M, ω_Y)` (biduality, with `M = 𝔻_Y L`), the
projection morphisms induce bijections on morphisms into `ω_Y`, `S ω_Y ≅ ω_X` and `φ : M' ⟶ N`
induces bijections on morphisms into `ω_X` after tensoring, then `S L ≅ RHom(N, ω_X)`
(`CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`). The internal homs are given by
arbitrary right adjoints of `M ⊗ -` and `N ⊗ -`, so that the statement can be applied to a
chosen model of the internal hom.

The bijectivity hypotheses, rather than invertibility, allow the projection morphism and `φ`
to be isomorphisms only "up to objects orthogonal to `ω`", as happens at the integral stage
`𝒪_E` of the `ℓ`-adic formalism, where they are isomorphisms modulo the uniformizer.

## Main statements

- `CategoryTheory.nonempty_iso_of_homEquiv`: the Yoneda lemma for a family of bijections.
- `CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`: the formal dual formula.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- Two objects with naturally equivalent `Hom`-functors are isomorphic: the Yoneda lemma, for
a family of bijections `(K ⟶ A) ≃ (K ⟶ B)` compatible with precomposition. -/
lemma nonempty_iso_of_homEquiv {C : Type*} [Category C] {A B : C}
    (e : ∀ K : C, (K ⟶ A) ≃ (K ⟶ B))
    (he : ∀ {K K' : C} (g : K' ⟶ K) (h : K ⟶ A), e K' (g ≫ h) = g ≫ e K h) :
    Nonempty (A ≅ B) := by
  refine ⟨⟨e A (𝟙 A), (e B).symm (𝟙 B), ?_, ?_⟩⟩
  · apply (e A).injective
    rw [he, Equiv.apply_symm_apply, Category.comp_id]
  · have := he (e B |>.symm (𝟙 B)) (𝟙 A)
    rw [Category.comp_id, Equiv.apply_symm_apply] at this
    exact this.symm

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

namespace Verdier

variable {P : C ⥤ D} {S : D ⥤ C}

/-- **The dual formula for the exceptional inverse image**, formally. Let `P ⊣ S` play the role
of `Rf_! ⊣ Rf^!`, let `L, M, ω_Y` be objects of `D` with an isomorphism `L ≅ RHom(M, ω_Y)`
(biduality, for `M = RHom(L, ω_Y)`), where `RHom(M, -)` is a right adjoint `H_M` of `M ⊗ -`,
and let `π_K : P K ⊗ M ⟶ P (K ⊗ M')` be a family natural in `K` (the projection morphism at
`M`, with `M' = f^* M`) inducing bijections on morphisms into `ω_Y`. Given `γ : S ω_Y ≅ ω_X`
and `φ : M' ⟶ N` inducing bijections `Hom(K ⊗ N, ω_X) ≃ Hom(K ⊗ M', ω_X)`, there is an
isomorphism `S L ≅ RHom(N, ω_X)`, for a right adjoint `H_N` of `N ⊗ -`. For every test object
`K` it is the chain of bijections
```
Hom(K, S L) ≃ Hom(P K, L) ≃ Hom(P K, RHom(M, ω_Y)) ≃ Hom(M ⊗ P K, ω_Y) ≃ Hom(P K ⊗ M, ω_Y)
  ≃ Hom(P (K ⊗ M'), ω_Y) ≃ Hom(K ⊗ M', S ω_Y) ≃ Hom(K ⊗ M', ω_X) ≃ Hom(K ⊗ N, ω_X)
  ≃ Hom(N ⊗ K, ω_X) ≃ Hom(K, RHom(N, ω_X)).
``` -/
theorem nonempty_iso_obj_of_adjunction (adj' : P ⊣ S) {L M ωY : D} {HM : D ⥤ D}
    (adjM : tensorLeft M ⊣ HM) (e : L ≅ HM.obj ωY) {M' : C}
    (π : ∀ K : C, P.obj K ⊗ M ⟶ P.obj (K ⊗ M'))
    (hπ : ∀ {K K' : C} (g : K' ⟶ K), P.map g ▷ M ≫ π K = π K' ≫ P.map (g ▷ M'))
    (hπω : ∀ K : C, Function.Bijective (fun a : P.obj (K ⊗ M') ⟶ ωY ↦ π K ≫ a))
    {ωX N : C} {HN : C ⥤ C} (adjN : tensorLeft N ⊣ HN) (γ : S.obj ωY ≅ ωX) (φ : M' ⟶ N)
    (hφ : ∀ K : C, Function.Bijective (fun a : K ⊗ N ⟶ ωX ↦ K ◁ φ ≫ a)) :
    Nonempty (S.obj L ≅ HN.obj ωX) := by
  let eπ (K : C) := Equiv.ofBijective _ (hπω K)
  let eφ (K : C) := Equiv.ofBijective _ (hφ K)
  have heπ {K K' : C} (g : K' ⟶ K) (w : P.obj K ⊗ M ⟶ ωY) :
      (eπ K').symm (P.map g ▷ M ≫ w) = P.map (g ▷ M') ≫ (eπ K).symm w := by
    apply (eπ K').injective
    simp only [Equiv.apply_symm_apply, eπ, Equiv.ofBijective_apply, ← reassoc_of% (hπ g)]
    congr 1
    exact ((eπ K).apply_symm_apply w).symm
  have heφ {K K' : C} (g : K' ⟶ K) (w : K ⊗ M' ⟶ ωX) :
      (eφ K').symm (g ▷ M' ≫ w) = g ▷ N ≫ (eφ K).symm w := by
    apply (eφ K').injective
    simp only [Equiv.apply_symm_apply, eφ, Equiv.ofBijective_apply]
    rw [whisker_exchange_assoc]
    congr 1
    exact ((eφ K).apply_symm_apply w).symm
  refine nonempty_iso_of_homEquiv (fun K ↦
    (adj'.homEquiv K L).symm.trans <| e.homToEquiv.trans <| (adjM.homEquiv _ _).symm.trans <|
      (β_ _ (P.obj K)).homFromEquiv.trans <| (eπ K).symm.trans <|
      (adj'.homEquiv _ _).trans <| γ.homToEquiv.trans <| (eφ K).symm.trans <|
      (β_ K N).homFromEquiv.trans <| adjN.homEquiv _ _) ?_
  intro K K' g h
  simp only [Equiv.trans_apply, Iso.homToEquiv_apply, Adjunction.homEquiv_naturality_left_symm,
    Category.assoc]
  have h₁ := BraidedCategory.braiding_inv_naturality_left (P.map g) M
  have h₂ := BraidedCategory.braiding_inv_naturality_right N g
  erw [Iso.homFromEquiv_apply, Iso.homFromEquiv_apply, ← reassoc_of% h₁]
  rw [heπ, Adjunction.homEquiv_naturality_left, Category.assoc, heφ, ← reassoc_of% h₂]
  exact adjN.homEquiv_naturality_left _ _

end Verdier

end CategoryTheory
