/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap

/-!
# Mates along rationalizations

Let `M` be a submonoid of `ℤ`, and let `T₁ : C₁ ⥤ D₁` and `T₂ : C₂ ⥤ D₂` be localization functors
of pretriangulated categories at the morphisms with `M`-torsion mapping cone
(`CategoryTheory.Rationalization.W`). Given adjunctions `L ⊣ R` between `C₁` and `C₂` and
`L' ⊣ R'` between `D₁` and `D₂`, with additive left adjoints, and an isomorphism
`τ : L ⋙ T₂ ≅ T₁ ⋙ L'`, the mate `R ⋙ T₁ ⟶ T₂ ⋙ R'` of `τ⁻¹` is an isomorphism
(`CategoryTheory.Rationalization.isIso_mateEquiv_of_isLocalization`).

Indeed, on `Hom` groups out of `T₁ A` it is the localization at `M` of the adjunction bijection
`Hom(A, R B) ≃ Hom(L A, B)`: morphisms `T X ⟶ T Y` are fractions `m⁻¹ • T f`
(`CategoryTheory.Rationalization.exists_smul_eq_map_of_isLocalization`), and `T f = T g` exactly
when `m • f = m • g` for some `m ∈ M`
(`CategoryTheory.Rationalization.map_eq_map_iff_of_isLocalization`).

This is how coefficient comparisons are transported along the rationalization
`D_cons(X, 𝒪_E)[1/ℓ] ≃ D_cons(X, E)`: a comparison defined as the mate of an isomorphism of left
adjoints (for instance the pushforward comparison, the mate of the pullback comparison) is an
isomorphism.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory

/-- The adjoint of `G f` followed by the mate of `τ⁻¹` is `τ⁻¹` followed by `H` of the adjoint
of `f`. -/
lemma Adjunction.homEquiv_symm_map_comp_mateEquiv_app {A B A' B' : Type*} [Category* A]
    [Category* B] [Category* A'] [Category* B'] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : A' ⥤ B'} {R' : B' ⥤ A'} (adj' : L' ⊣ R') (G : A ⥤ A') (H : B ⥤ B')
    (τ : L ⋙ H ≅ G ⋙ L') {M : A} {N : B} (f : M ⟶ R.obj N) :
    (adj'.homEquiv _ _).symm
        (G.map f ≫ (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ τ.inv)).app N) =
      τ.inv.app M ≫ H.map ((adj.homEquiv _ _).symm f) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    mateEquiv_counit, Functor.map_comp]
  exact τ.inv.naturality_assoc f _

namespace Rationalization

variable {M : Submonoid ℤ}
  {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁] [IsTriangulated C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂] [IsTriangulated C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Preadditive D₁]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Preadditive D₂]

/-- For a localization functor `L` at the morphisms with `M`-torsion mapping cone, two morphisms
have the same image if and only if they agree after multiplication by an element of `M`. -/
lemma map_eq_map_iff_of_isLocalization (T : C₁ ⥤ D₁) [T.IsLocalization (W M C₁)] [T.Additive]
    {X Y : C₁} (f g : X ⟶ Y) :
    T.map f = T.map g ↔ ∃ m ∈ M, m • f = m • g := by
  constructor
  · intro h
    obtain ⟨Z, s, hs, hfs⟩ := (MorphismProperty.map_eq_iff_postcomp T (W M C₁) f g).1 h
    obtain ⟨m, hm, t, ht⟩ := exists_comp_eq_smul_id hs
    refine ⟨m, hm, ?_⟩
    rw [← comp_id f, ← comp_id g, ← Linear.comp_smul, ← Linear.comp_smul, ← ht,
      ← assoc, hfs, assoc]
  · rintro ⟨m, hm, h⟩
    have : IsIso (T.map (m • 𝟙 X)) := Localization.inverts T (W M C₁) _ (W_smul_id hm X)
    rw [← cancel_epi (T.map (m • 𝟙 X)), ← T.map_comp, ← T.map_comp, Linear.smul_comp,
      Linear.smul_comp, id_comp, id_comp, h]

omit [IsTriangulated C₁] in
/-- For a localization functor at the morphisms with `M`-torsion mapping cone, multiplication by
`m ∈ M` on `T X` is an isomorphism. -/
lemma isIso_smul_id_map_obj (T : C₁ ⥤ D₁) [T.IsLocalization (W M C₁)] [T.Additive] {m : ℤ}
    (hm : m ∈ M) (X : C₁) : IsIso (m • 𝟙 (T.obj X)) := by
  rw [← T.map_id, ← Functor.map_zsmul]
  exact Localization.inverts T (W M C₁) _ (W_smul_id hm X)

variable (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂) [T₁.IsLocalization (W M C₁)] [T₂.IsLocalization (W M C₂)]
  [T₁.Additive] [T₂.Additive]
  {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R) {L' : D₁ ⥤ D₂} {R' : D₂ ⥤ D₁} (adj' : L' ⊣ R')
  [L.Additive] [L'.Additive] (τ : L ⋙ T₂ ≅ T₁ ⋙ L')

include M in
/-- **Mates along rationalizations are isomorphisms**: for localization functors `T₁`, `T₂` at the
morphisms with `M`-torsion mapping cone, adjunctions `L ⊣ R` and `L' ⊣ R'` with additive left
adjoints, and an isomorphism `τ : L ⋙ T₂ ≅ T₁ ⋙ L'`, the mate `R ⋙ T₁ ⟶ T₂ ⋙ R'` of `τ⁻¹` is an
isomorphism. On `Hom(T₁ A, -)` it is the localization at `M` of the adjunction bijection. -/
theorem isIso_mateEquiv_of_isLocalization :
    IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ τ.inv)) := by
  have hadj (A : C₁) (B : C₂) (m : ℤ) (f : A ⟶ R.obj B) :
      (adj.homEquiv _ _).symm (m • f) = m • (adj.homEquiv _ _).symm f := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_zsmul,
      Linear.smul_comp]
  have hadj' (A : D₁) (B : D₂) (m : ℤ) (f : A ⟶ R'.obj B) :
      (adj'.homEquiv _ _).symm (m • f) = m • (adj'.homEquiv _ _).symm f := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_zsmul,
      Linear.smul_comp]
  have key (A : C₁) (B : C₂) (f : A ⟶ R.obj B) :=
    Adjunction.homEquiv_symm_map_comp_mateEquiv_app adj adj' T₁ T₂ τ f
  set β := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ τ.inv))
  have hA (A : C₁) (B : C₂) :
      Function.Bijective (fun x : T₁.obj A ⟶ T₁.obj (R.obj B) ↦ x ≫ β.app B) := by
    have h0 : (adj'.homEquiv (T₁.obj A) (T₂.obj B)).symm 0 = 0 := by
      simpa using hadj' _ _ 0 0
    refine ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
    · rw [← sub_eq_zero]
      have hδ : (x - y) ≫ β.app B = 0 := by
        rw [Preadditive.sub_comp]
        exact sub_eq_zero.2 hxy
      obtain ⟨m, hm, θ, hθ⟩ := exists_smul_eq_map_of_isLocalization (M := M) T₁ (x - y)
      have h1 : T₂.map ((adj.homEquiv _ _).symm θ) = T₂.map 0 := by
        have := key A B θ
        rw [← hθ, Linear.smul_comp, hδ, smul_zero, h0] at this
        rw [Functor.map_zero, ← cancel_epi (τ.inv.app A), ← this, comp_zero]
      obtain ⟨m', hm', h2⟩ := (map_eq_map_iff_of_isLocalization (M := M) T₂ _ _).1 h1
      rw [smul_zero, ← hadj] at h2
      have h3 : m' • θ = 0 :=
        (adj.homEquiv _ _).symm.injective (h2.trans (by simpa using (hadj A B 0 0).symm))
      have := isIso_smul_id_map_obj T₁ (M.mul_mem hm' hm) A
      rw [← cancel_epi ((m' * m) • 𝟙 (T₁.obj A)), comp_zero, Linear.smul_comp, id_comp,
        mul_smul, hθ, ← Functor.map_zsmul, h3, Functor.map_zero]
    · obtain ⟨m, hm, η, hη⟩ := exists_smul_eq_map_of_isLocalization (M := M) T₂
        (τ.hom.app A ≫ (adj'.homEquiv _ _).symm φ)
      have := isIso_smul_id_map_obj T₁ hm A
      refine ⟨CategoryTheory.inv (m • 𝟙 (T₁.obj A)) ≫ T₁.map (adj.homEquiv _ _ η), ?_⟩
      have h1 : T₁.map (adj.homEquiv _ _ η) ≫ β.app B = m • φ := by
        apply (adj'.homEquiv _ _).symm.injective
        rw [key, Equiv.symm_apply_apply, ← hη, hadj', Linear.comp_smul, Iso.inv_hom_id_app_assoc]
      have h2 : m • φ = (m • 𝟙 (T₁.obj A)) ≫ φ := by rw [Linear.smul_comp, id_comp]
      dsimp only
      rw [assoc, h1, h2, IsIso.inv_hom_id_assoc]
  have (B : C₂) : IsIso (β.app B) := by
    have := Localization.essSurj T₁ (W M C₁)
    refine isIso_of_yoneda_map_bijective _ fun Z ↦ ?_
    let e := T₁.objObjPreimageIso Z
    obtain ⟨hi, hs⟩ := hA (T₁.objPreimage Z) B
    refine ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
    · rw [← cancel_epi e.hom]
      exact hi (by simpa only [assoc] using e.hom ≫= hxy)
    · obtain ⟨y, hy⟩ := hs (e.hom ≫ φ)
      exact ⟨e.inv ≫ y, by simpa only [assoc, Iso.inv_hom_id_assoc] using e.inv ≫= hy⟩
  exact NatIso.isIso_of_isIso_app β

end Rationalization

end CategoryTheory
