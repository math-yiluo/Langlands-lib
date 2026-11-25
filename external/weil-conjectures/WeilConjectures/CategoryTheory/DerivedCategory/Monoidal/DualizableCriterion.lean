/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# A chain-level criterion for dualizability in the derived category

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and `K(C)` its homotopy category. For a K-flat complex `P`, K-injective resolutions
`u : 𝟙 ⟶ I₁` of the unit and `i : P ⟶ I` of `P`, and a map `j : I₁ ⊗ P ⟶ I` with
`u ▷ P ≫ j = λ ≫ i`, the canonical comparison `[P, 𝟙] ⊗ P ⟶ [P, P]` of `D(C)` is the image of
the chain-level map `χ : iHom(P, I₁) ⊗ P ⟶ iHom(P, I)` adjoint to
`P ⊗ (iHom(P, I₁) ⊗ P) ≅ (P ⊗ iHom(P, I₁)) ⊗ P ⟶ I₁ ⊗ P ⟶ I`. So `Qh.obj P` is dualizable if and
only if `Qh.map χ` is an isomorphism (`DerivedCategory.isDualizable_Qh_obj_iff`).

The point of this criterion is that it is stated in terms of complexes, so that it can be
transported along exact monoidal functors which commute with internal homs.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_curry_of_bijective`: a map `e : X ⊗ H ⟶ M` such that
  `f ↦ X ◁ f ≫ e` is bijective exhibits `H` as `[X, M]`.
- `CategoryTheory.MonoidalClosed.isDualizable_iff_isIso_ihomUnitTensorToIhom`: in a braided
  monoidal closed category, `X` is dualizable if and only if `[X, 𝟙] ⊗ X ⟶ [X, X]` is an
  isomorphism.
- `DerivedCategory.isIso_curry_μ_Qh_counit`: for `P` K-flat and `Y` K-injective, the internal hom
  `[Qh P, Qh Y]` of `D(C)` is `Qh (iHom(P, Y))`.
- `DerivedCategory.isDualizable_Qh_obj_iff`: the chain-level criterion.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- A map `e : X ⊗ H ⟶ M` such that `f ↦ X ◁ f ≫ e` is bijective on maps `T ⟶ H` for every `T`
exhibits `H` as the internal hom `[X, M]`: the transpose `H ⟶ [X, M]` of `e` is an isomorphism. -/
lemma isIso_curry_of_bijective {X H M : C} (e : X ⊗ H ⟶ M)
    (he : ∀ T : C, Function.Bijective (fun f : T ⟶ H ↦ X ◁ f ≫ e)) : IsIso (curry e) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have : (fun f : T ⟶ H ↦ f ≫ curry e) = curry ∘ (fun f : T ⟶ H ↦ X ◁ f ≫ e) := by
    ext f
    simp [curry_natural_left]
  rw [this]
  exact ((ihom.adjunction X).homEquiv T M).bijective.comp (he T)

variable [BraidedCategory C]

/-- In a braided monoidal closed category, an object `X` is dualizable if and only if the
canonical comparison `[X, 𝟙] ⊗ X ⟶ [X, X]` is an isomorphism. -/
lemma isDualizable_iff_isIso_ihomUnitTensorToIhom (X : C) :
    IsDualizable X ↔ IsIso (ihomUnitTensorToIhom X X) := by
  refine ⟨fun ⟨_⟩ ↦ ?_, fun _ ↦ ?_⟩
  · let := BraidedCategory.exactPairing_swap X Xᘁ
    exact isIso_ihomUnitTensorToIhom Xᘁ X X
  · let := exactPairingOfIsIso X
    exact ⟨{ rightDual := _, exact := BraidedCategory.exactPairing_swap ((ihom X).obj (𝟙_ C)) X }⟩

end CategoryTheory.MonoidalClosed

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

local instance instHasColimitsOfSize_dualizableCriterion
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

open HomotopyCategory MonoidalClosed

/-- The lax monoidal structure `Qh K ⊗ᴸ Qh L ⟶ Qh (K ⊗ L)` is an isomorphism when `L` is
K-flat. -/
lemma isIso_μ_Qh_of_kFlat_right (K L : HomotopyCategory C (.up ℤ))
    (hL : (quasiIso C (.up ℤ)).kFlat L) : IsIso (μ Qh K L) :=
  have := isLeftDerivedFunctor₂CurriedTensor C
  (MorphismProperty.id_prod_kFlat_derives_curriedTensor (quasiIso C (.up ℤ))
    Qh).isIso_of_isLeftDerivabilityStructure (LF := curriedTensor (DerivedCategory C))
      (μNatTrans Qh) K ⟨L, hL⟩

omit [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
/-- Maps into a K-injective object of `K(C)`, that is a local object for the quasi-isomorphisms,
are the maps in `D(C)`. -/
lemma Qh_map_bijective_of_isLocal {Y : HomotopyCategory C (.up ℤ)}
    (hY : (quasiIso C (.up ℤ)).isLocal Y) (X : HomotopyCategory C (.up ℤ)) :
    Function.Bijective (Qh.map : (X ⟶ Y) → _) := by
  have : (subcategoryAcyclic C).rightOrthogonal Y := by
    rw [← ObjectProperty.isLocal_trW, ← quasiIso_eq_trW_subcategoryAcyclic]
    exact hY
  exact this.map_bijective_of_isTriangulated Qh X

section InternalHom

variable {P Y : HomotopyCategory C (.up ℤ)}

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C] in
/-- For `P` K-flat and `Y` K-injective, the internal hom complex `iHom(P, Y)` is K-injective:
maps into it are maps out of `P ⊗ -` into `Y`, and `P ⊗ -` preserves quasi-isomorphisms. -/
lemma isLocal_internalHom_obj (hP : (quasiIso C (.up ℤ)).kFlat P)
    (hY : (quasiIso C (.up ℤ)).isLocal Y) :
    (quasiIso C (.up ℤ)).isLocal ((internalHom P).obj Y) := by
  intro X X' s hs
  let adj := tensorHomAdjunction P
  have : (fun g : X' ⟶ (internalHom P).obj Y ↦ s ≫ g) =
      adj.homEquiv X Y ∘ (fun h ↦ P ◁ s ≫ h) ∘ (adj.homEquiv X' Y).symm := by
    ext g
    simp only [Function.comp_apply]
    erw [← adj.homEquiv_naturality_left_symm, Equiv.apply_symm_apply]
  rw [this]
  exact (adj.homEquiv X Y).bijective.comp
    ((hY _ (hP.whiskerLeft hs)).comp (adj.homEquiv X' Y).symm.bijective)

/-- For `P` K-flat and `Y` K-injective, maps `T ⟶ Qh (iHom(P, Y))` in `D(C)` are maps
`Qh P ⊗ T ⟶ Qh Y`, by whiskering with the image of the evaluation of complexes. -/
lemma bijective_whiskerLeft_comp_μ_Qh_counit (hP : (quasiIso C (.up ℤ)).kFlat P)
    (hY : (quasiIso C (.up ℤ)).isLocal Y) (T : DerivedCategory C) :
    Function.Bijective (fun f : T ⟶ Qh.obj ((internalHom P).obj Y) ↦
      Qh.obj P ◁ f ≫ μ Qh P _ ≫ Qh.map ((tensorHomAdjunction P).counit.app Y)) := by
  let E := μ Qh P _ ≫ Qh.map ((tensorHomAdjunction P).counit.app Y)
  have hT (T' : HomotopyCategory C (.up ℤ)) :
      Function.Bijective (fun f : Qh.obj T' ⟶ Qh.obj ((internalHom P).obj Y) ↦
        Qh.obj P ◁ f ≫ E) := by
    have := isIso_μ_Qh_of_kFlat P T' hP
    rw [← Function.Bijective.of_comp_iff _
      (Qh_map_bijective_of_isLocal (isLocal_internalHom_obj hP hY) T')]
    have : (fun f : Qh.obj T' ⟶ Qh.obj ((internalHom P).obj Y) ↦ Qh.obj P ◁ f ≫ E) ∘
        Qh.map = (fun g ↦ μ Qh P T' ≫ g) ∘ Qh.map ∘
          ((tensorHomAdjunction P).homEquiv T' Y).symm := by
      ext f
      simp only [Function.comp_apply, Adjunction.homEquiv_counit, E]
      simp
    rw [this]
    refine Function.Bijective.comp ?_ ((Qh_map_bijective_of_isLocal hY _).comp
      (Equiv.bijective _))
    exact (Function.bijective_iff_has_inverse).2 ⟨fun g ↦ inv (μ Qh P T') ≫ g,
      fun g ↦ by simp, fun g ↦ by simp⟩
  let e := Qh.objObjPreimageIso T
  have : (fun f : T ⟶ Qh.obj ((internalHom P).obj Y) ↦ Qh.obj P ◁ f ≫ E) =
      (fun g ↦ Qh.obj P ◁ e.inv ≫ g) ∘
        (fun f : Qh.obj (Qh.objPreimage T) ⟶ _ ↦ Qh.obj P ◁ f ≫ E) ∘ (fun f ↦ e.hom ≫ f) := by
    ext f
    simp
  rw [this]
  refine Function.Bijective.comp ?_ ((hT _).comp ?_)
  · exact (Function.bijective_iff_has_inverse).2 ⟨fun g ↦ Qh.obj P ◁ e.hom ≫ g,
      fun g ↦ by simp, fun g ↦ by simp⟩
  · exact (Function.bijective_iff_has_inverse).2 ⟨fun g ↦ e.inv ≫ g,
      fun g ↦ by simp, fun g ↦ by simp⟩

/-- For `P` K-flat and `Y` K-injective, `[Qh P, Qh Y]` is `Qh (iHom(P, Y))`: the transpose of
the image of the evaluation `P ⊗ iHom(P, Y) ⟶ Y`, followed by any isomorphism, is an
isomorphism. -/
lemma isIso_curry_μ_Qh_counit_comp (hP : (quasiIso C (.up ℤ)).kFlat P)
    (hY : (quasiIso C (.up ℤ)).isLocal Y) {M : DerivedCategory C} (φ : Qh.obj Y ⟶ M)
    [IsIso φ] :
    IsIso (curry (μ Qh P _ ≫ Qh.map ((tensorHomAdjunction P).counit.app Y) ≫ φ)) := by
  have := isIso_curry_of_bijective _ (bijective_whiskerLeft_comp_μ_Qh_counit hP hY)
  rw [← Category.assoc, curry_natural_right]
  infer_instance

end InternalHom

/-- **A chain-level criterion for dualizability.** Let `P` be a K-flat complex, `u : 𝟙 ⟶ I₁` and
`i : P ⟶ I` K-injective resolutions, `j : I₁ ⊗ P ⟶ I` with `u ▷ P ≫ j = λ ≫ i`, and
`χ : iHom(P, I₁) ⊗ P ⟶ iHom(P, I)` the transpose of
`P ⊗ (iHom(P, I₁) ⊗ P) ≅ (P ⊗ iHom(P, I₁)) ⊗ P ⟶ I₁ ⊗ P ⟶ I`. Then `Qh P` is dualizable in
`D(C)` if and only if `χ` is a quasi-isomorphism: `Qh χ` is the comparison
`[Qh P, 𝟙] ⊗ Qh P ⟶ [Qh P, Qh P]`, up to isomorphisms. -/
theorem isDualizable_Qh_obj_iff {P I₁ I : HomotopyCategory C (.up ℤ)}
    (hP : (quasiIso C (.up ℤ)).kFlat P) (hI₁ : (quasiIso C (.up ℤ)).isLocal I₁)
    (hI : (quasiIso C (.up ℤ)).isLocal I) (u : 𝟙_ _ ⟶ I₁) [IsIso (Qh.map u)] (i : P ⟶ I)
    [IsIso (Qh.map i)] (j : I₁ ⊗ P ⟶ I) (hj : u ▷ P ≫ j = (λ_ P).hom ≫ i)
    (χ : (internalHom P).obj I₁ ⊗ P ⟶ (internalHom P).obj I)
    (hχ : P ◁ χ ≫ (tensorHomAdjunction P).counit.app I =
      (α_ _ _ _).inv ≫ (tensorHomAdjunction P).counit.app I₁ ▷ P ≫ j) :
    IsDualizable (Qh.obj P) ↔ IsIso (Qh.map χ) := by
  let ev₁ := (tensorHomAdjunction P).counit.app I₁
  let evI := (tensorHomAdjunction P).counit.app I
  let e₁ := μ Qh P _ ≫ Qh.map ev₁ ≫ (inv (Qh.map u) ≫ inv (ε Qh))
  let f := μ Qh P _ ≫ Qh.map evI ≫ inv (Qh.map i)
  have hc₁ : IsIso (curry e₁) := isIso_curry_μ_Qh_counit_comp hP hI₁ _
  have hc : IsIso (curry f) := isIso_curry_μ_Qh_counit_comp hP hI _
  have hμ : IsIso (μ Qh ((internalHom P).obj I₁) P) := isIso_μ_Qh_of_kFlat_right _ _ hP
  let m := μ Qh ((internalHom P).obj I₁) P ≫ Qh.map χ
  -- the unit part
  have hunit : μ Qh I₁ P ≫ Qh.map j ≫ inv (Qh.map i) =
      (inv (Qh.map u) ≫ inv (ε Qh)) ▷ Qh.obj P ≫ (λ_ _).hom := by
    rw [← cancel_epi ((ε Qh ≫ Qh.map u) ▷ Qh.obj P), ← comp_whiskerRight_assoc,
      Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, id_whiskerRight,
      Category.id_comp, comp_whiskerRight_assoc, μ_natural_left_assoc, ← Functor.map_comp_assoc,
      hj, Functor.map_comp_assoc, IsIso.hom_inv_id, Category.comp_id, left_unitality]
  have key : Qh.obj P ◁ m ≫ f = (α_ _ _ _).inv ≫ e₁ ▷ Qh.obj P ≫ (λ_ _).hom := by
    simp only [m, f, e₁, MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right_assoc]
    rw [← Functor.map_comp_assoc Qh (P ◁ χ) evI, hχ, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, associativity_inv_assoc, ← μ_natural_left_assoc]
    erw [hunit]
    simp only [comp_whiskerRight, Category.assoc]
    rfl
  have sq : curry e₁ ▷ Qh.obj P ≫ ihomUnitTensorToIhom (Qh.obj P) (Qh.obj P) = m ≫ curry f := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, key, uncurry_eq,
      whiskerLeft_ihomUnitTensorToIhom_ev,
      associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ← uncurry_eq,
      uncurry_curry]
  obtain ⟨_⟩ := nonempty_braidedCategory C
  rw [isDualizable_iff_isIso_ihomUnitTensorToIhom]
  have hθ : ihomUnitTensorToIhom (Qh.obj P) (Qh.obj P) =
      inv (curry e₁ ▷ Qh.obj P) ≫ m ≫ curry f := by
    rw [← sq, IsIso.inv_hom_id_assoc]
  rw [hθ]
  constructor
  · intro h
    have : IsIso m := by
      have : IsIso (m ≫ curry f) := by
        rw [← IsIso.hom_inv_id_assoc (curry e₁ ▷ Qh.obj P) (m ≫ curry f)]
        infer_instance
      exact IsIso.of_isIso_comp_right m (curry f)
    exact IsIso.of_isIso_comp_left (μ Qh ((internalHom P).obj I₁) P) (Qh.map χ)
  · intro _
    infer_instance

end DerivedCategory
