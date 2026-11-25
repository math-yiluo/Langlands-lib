/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Natural isomorphisms with specified scalar-localized components

Source: blueprint sk-def-sf-operations, raw rationalization Hom formula.
(blueprint: lem-pur-scalar-localization-component-iso)
-/

@[expose] public section
set_option autoImplicit false
open TensorProduct
namespace CategoryTheory.ScalarLocalization

/-- Compatible component formulas lift an ordinary natural isomorphism uniquely.
Source: blueprint sk-def-sf-operations, raw rationalization Hom formula
(blueprint: lem-pur-scalar-localization-component-iso).
Proof: conjugate each localized component by the given object identifications.
For naturality, induct on scalar-first tensors in the localized Hom group. The zero
and sum cases follow from additivity. For a pure tensor use the specified formulas
for both functors, the pure-tensor composition formula, and ordinary naturality.
The conjugating object equalities cancel. Componentwise equality gives uniqueness.
This includes zero rings and arbitrary functions on scalars: the assumptions on the
two existing functors already provide all compatibility needed for naturality. -/
theorem existsUnique_iso_of_component_formulas
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    simp [c]
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    change Localization.Away t ⊗[R] (K ⟶ K') at f
    induction f using TensorProduct.inductionOn with
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
        (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
      dsimp [c]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      simpa only [ScalarLocalization.localization, Category.assoc] using
        congrArg (fun z :
          (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
            eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

end CategoryTheory.ScalarLocalization
