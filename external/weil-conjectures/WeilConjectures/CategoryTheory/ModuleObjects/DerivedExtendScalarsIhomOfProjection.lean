/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs along adjunctions satisfying the projection formula at the unit

Let `L : C ⥤ D` be a monoidal functor between monoidal closed categories, with a right adjoint
`H` reflecting isomorphisms, and write `P = H 𝟙`. Suppose that the left projection morphisms
`K ⊗ P ⟶ H (L K ⊗ 𝟙)` (`CategoryTheory.Adjunction.leftProjectionMorphism`) are isomorphisms, so
that `H L K ≅ K ⊗ P` naturally, and that `P` has a left dual. Then the comparison maps
`L [A, B] ⟶ [L A, L B]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) are isomorphisms
(`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism`).

Informally, `H L [A, B] ≅ [A, B] ⊗ P ≅ [A, B ⊗ P] ≅ [A, H L B] ≅ H [L A, L B]`, the middle
isomorphism holding because `P` is dualizable. The proof is a Yoneda argument: for every `X`,
transposing `X ⟶ H [L A, L B]` to `A ⊗ X ⟶ H L B` and writing morphisms into `H L K` as morphisms
into `K ⊗ P`, the comparison becomes `g ↦ A ◁ g ≫ α⁻¹ ≫ ev ▷ P`
(`CategoryTheory.Functor.LaxMonoidal.homEquiv_δ_uncurry_leftProjectionMorphism`), a bijection for
dualizable `P` (`CategoryTheory.Functor.LaxMonoidal.bijective_whiskerLeft_comp_ev_whiskerRight`).

This applies to the derived extension of scalars along a quotient `R ⟶ R ⧸ k` by a
nonzerodivisor (`CategoryTheory.Mod.isIso_ihomComparison_leftDerivedExtendScalars`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

namespace Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- The left projection morphism `K ⊗ H 𝟙 ⟶ H (L K ⊗ 𝟙)` followed by the right unitor is the
transpose of `L (K ⊗ H 𝟙) ⟶ L K ⊗ L H 𝟙 ⟶ L K ⊗ 𝟙 ≅ L K`. -/
lemma leftProjectionMorphism_comp_map_rightUnitor (L : C ⥤ D) [L.OplaxMonoidal] {H : D ⥤ C}
    (adj : L ⊣ H) (K : C) :
    adj.leftProjectionMorphism K (𝟙_ D) ≫ H.map (ρ_ _).hom =
      adj.homEquiv _ _ ((OplaxMonoidal.δ L K _ ≫ L.obj K ◁ adj.counit.app _) ≫ (ρ_ _).hom) := by
  rw [adj.homEquiv_naturality_right]
  rfl

/-- A coherence for the comonoidal structure of a monoidal functor `L`: for `e : L P ⟶ 𝟙` and
`ev : A ⊗ K ⟶ B`, the two ways from `L (A ⊗ (K ⊗ P))` to `L B` through `L A ⊗ L K` and through
`L B ⊗ L P` agree. -/
lemma δ_whiskerLeft_δ_rightUnitor_μ (L : C ⥤ D) [L.Monoidal] (A K P : C) {B : C}
    (e : L.obj P ⟶ 𝟙_ D) (ev : A ⊗ K ⟶ B) :
    OplaxMonoidal.δ L A (K ⊗ P) ≫ L.obj A ◁ (OplaxMonoidal.δ L K P ≫ L.obj K ◁ e ≫
      (ρ_ (L.obj K)).hom) ≫ μ L A K ≫ L.map ev =
    L.map (α_ A K P).inv ≫ L.map (ev ▷ P) ≫ OplaxMonoidal.δ L B P ≫ L.obj B ◁ e ≫
      (ρ_ (L.obj B)).hom := by
  have hA : OplaxMonoidal.δ L A (K ⊗ P) ≫ L.obj A ◁ OplaxMonoidal.δ L K P =
      L.map (α_ A K P).inv ≫ OplaxMonoidal.δ L (A ⊗ K) P ≫ OplaxMonoidal.δ L A K ▷ L.obj P ≫
        (α_ _ _ _).hom := by
    rw [← OplaxMonoidal.associativity_inv_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← OplaxMonoidal.δ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    reassoc_of% hA, MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_rightUnitor,
    Category.assoc, ← associator_naturality_right_assoc, Iso.hom_inv_id_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality_assoc, Monoidal.δ_μ_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

variable [MonoidalClosed C] [MonoidalClosed D]

/-- The Yoneda computation behind
`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism`:
transposing `g ≫ σ ≫ H w` (with `σ : [A, B] ⊗ H 𝟙 ⟶ H L [A, B]` the left projection morphism
followed by the right unitor, and `w` the comparison map of `L`) along `L ⊣ H` and the
tensor-hom adjunctions gives `A ◁ g ≫ α⁻¹ ≫ ev ▷ H 𝟙 ≫ σ`. -/
lemma homEquiv_δ_uncurry_leftProjectionMorphism (L : C ⥤ D) [L.Monoidal] {H : D ⥤ C}
    (adj : L ⊣ H) {A B X : C} (g : X ⟶ (ihom A).obj B ⊗ H.obj (𝟙_ D)) :
    adj.homEquiv _ _ (OplaxMonoidal.δ L A X ≫ uncurry ((adj.homEquiv _ _).symm
      ((g ≫ adj.leftProjectionMorphism _ (𝟙_ D) ≫ H.map (ρ_ _).hom) ≫
        H.map ((ihomComparison L A).app B)))) =
    A ◁ g ≫ (α_ _ _ _).inv ≫ (ihom.ev A).app B ▷ _ ≫ adj.leftProjectionMorphism B (𝟙_ D) ≫
      H.map (ρ_ _).hom := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, leftProjectionMorphism_comp_map_rightUnitor,
    leftProjectionMorphism_comp_map_rightUnitor, ← adj.homEquiv_naturality_left,
    ← adj.homEquiv_naturality_right, Equiv.symm_apply_apply]
  erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left,
    ← adj.homEquiv_naturality_left, Equiv.symm_apply_apply]
  rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc, ihomComparison_ev,
    MonoidalCategory.whiskerLeft_comp_assoc, OplaxMonoidal.δ_natural_right_assoc]
  simp only [Category.assoc]
  congr 1
  exact δ_whiskerLeft_δ_rightUnitor_μ L A _ _ _ _

/-- The map `g ↦ A ◁ g ≫ α⁻¹ ≫ ev ▷ P`, `(X ⟶ [A, B] ⊗ P) ⟶ (A ⊗ X ⟶ B ⊗ P)`, is bijective when
`P` has a left dual: through the bijections `(X ⟶ [A, B] ⊗ P) ≃ (X ⊗ P' ⟶ [A, B])` and
`(A ⊗ X ⟶ B ⊗ P) ≃ ((A ⊗ X) ⊗ P' ⟶ B)` it is uncurrying. -/
lemma bijective_whiskerLeft_comp_ev_whiskerRight (P' P : C) [ExactPairing P' P] (A B X : C) :
    Function.Bijective (fun g : X ⟶ (ihom A).obj B ⊗ P ↦
      (A ◁ g ≫ (α_ _ _ _).inv ≫ (ihom.ev A).app B ▷ P : A ⊗ X ⟶ B ⊗ P)) := by
  have h (f : X ⊗ P' ⟶ (ihom A).obj B) :
      (A ◁ tensorRightHomEquiv X P' P _ f ≫ (α_ _ _ _).inv ≫ (ihom.ev A).app B ▷ P :
        A ⊗ X ⟶ B ⊗ P) = tensorRightHomEquiv (A ⊗ X) P' P B ((α_ _ _ _).hom ≫ uncurry f) := by
    simp only [tensorRightHomEquiv, Equiv.coe_fn_mk, uncurry_eq]
    monoidal
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun y ↦ ?_⟩
  · dsimp only at hg
    rw [← (tensorRightHomEquiv X P' P _).apply_symm_apply g₁,
      ← (tensorRightHomEquiv X P' P _).apply_symm_apply g₂] at hg ⊢
    rw [h, h] at hg
    rw [uncurry_injective ((cancel_epi _).1 ((tensorRightHomEquiv _ _ _ _).injective hg))]
  · refine ⟨tensorRightHomEquiv X P' P _
      (curry ((α_ A X P').inv ≫ (tensorRightHomEquiv (A ⊗ X) P' P B).symm y)), ?_⟩
    dsimp only
    rw [h, uncurry_curry, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]

/-- **Internal homs along an adjunction satisfying the projection formula at the unit.** Let
`L : C ⥤ D` be a monoidal functor between monoidal closed categories with a right adjoint `H`
reflecting isomorphisms. If `H 𝟙` has a left dual `P'` and the left projection morphisms
`K ⊗ H 𝟙 ⟶ H (L K ⊗ 𝟙)` are isomorphisms, then the comparison maps `L [A, B] ⟶ [L A, L B]` are
isomorphisms. -/
theorem isIso_ihomComparison_of_isIso_leftProjectionMorphism (L : C ⥤ D) [L.Monoidal]
    {H : D ⥤ C} [H.ReflectsIsomorphisms] (adj : L ⊣ H) (P' : C) [ExactPairing P' (H.obj (𝟙_ D))]
    (h : ∀ K : C, IsIso (adj.leftProjectionMorphism K (𝟙_ D))) (A B : C) :
    IsIso ((ihomComparison L A).app B) := by
  rw [← isIso_iff_of_reflects_iso _ H, isIso_iff_yoneda_map_bijective]
  intro X
  let e : (X ⟶ H.obj ((ihom (L.obj A)).obj (L.obj B))) → (A ⊗ X ⟶ H.obj (L.obj B)) :=
    fun y ↦ adj.homEquiv _ _ (OplaxMonoidal.δ L A X ≫ uncurry ((adj.homEquiv _ _).symm y))
  have he : Function.Injective e := fun a b hab ↦ (adj.homEquiv _ _).symm.injective
    (uncurry_injective ((cancel_epi (OplaxMonoidal.δ L A X)).1
      ((adj.homEquiv _ _).injective hab)))
  have hσ (K : C) : IsIso (adj.leftProjectionMorphism K (𝟙_ D) ≫ H.map (ρ_ _).hom) := by
    have := h K
    infer_instance
  have hα : Function.Bijective (fun g : X ⟶ (ihom A).obj B ⊗ H.obj (𝟙_ D) ↦
      g ≫ adj.leftProjectionMorphism _ (𝟙_ D) ≫ H.map (ρ_ _).hom) :=
    (isIso_iff_yoneda_map_bijective _).1 (hσ _) X
  have hβ : Function.Bijective (fun f : A ⊗ X ⟶ B ⊗ H.obj (𝟙_ D) ↦
      f ≫ adj.leftProjectionMorphism B (𝟙_ D) ≫ H.map (ρ_ _).hom) :=
    (isIso_iff_yoneda_map_bijective _).1 (hσ _) _
  have hcomp : Function.Bijective
      ((e ∘ fun g ↦ g ≫ H.map ((ihomComparison L A).app B)) ∘
        fun g : X ⟶ (ihom A).obj B ⊗ H.obj (𝟙_ D) ↦
          g ≫ adj.leftProjectionMorphism _ (𝟙_ D) ≫ H.map (ρ_ _).hom) := by
    convert hβ.comp (bijective_whiskerLeft_comp_ev_whiskerRight P' _ A B X) using 1
    funext g
    exact (homEquiv_δ_uncurry_leftProjectionMorphism L adj g).trans
      (by simp only [Function.comp_apply, Category.assoc])
  rw [Function.Bijective.of_comp_iff _ hα] at hcomp
  refine ⟨hcomp.1.of_comp, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcomp.2 (e y)
  exact ⟨x, he hx⟩

end Functor.LaxMonoidal

end CategoryTheory
