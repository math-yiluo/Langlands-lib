/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

/-! # Recovering an isomorphism from its punctured zero slice

## References

* Stacks Project, Tag 0EY9
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Full faithfulness, or an isomorphic base, lifts a splitting from a base change. -/
theorem powerSeries_punctured_split_assembly
    {B W E F : Scheme.{u}} (z : W ⟶ B) (p : E ⟶ B) (r : F ⟶ B)
    [IsFinite p] [Etale p] [IsFinite r] [Etale r]
    (hfull : IsIso z ∨ ∀ P Q : B.FiniteEtale,
      Function.Bijective ((FiniteEtale.pullback z).map (X := P) (Y := Q)))
    (e₀ : pullback p z ≅ pullback r z)
    (he₀ : e₀.hom ≫ pullback.snd r z = pullback.snd p z) :
    ∃ e : E ≅ F, e.hom ≫ r = p := by
  classical
  rcases hfull with hz | hfull
  · let := hz
    let a := asIso (pullback.fst p z)
    let b := asIso (pullback.fst r z)
    refine ⟨a.symm ≪≫ e₀ ≪≫ b, ?_⟩
    change (a.inv ≫ e₀.hom ≫ b.hom) ≫ r = p
    simp only [Category.assoc]
    rw [show b.hom ≫ r = pullback.snd r z ≫ z from pullback.condition]
    rw [← Category.assoc e₀.hom, he₀]
    rw [← pullback.condition, ← Category.assoc]
    exact a.inv_hom_id_assoc p
  · let P : B.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ p inferInstance,
        (by exact inferInstanceAs (IsFinite p))⟩
    let Q : B.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ r inferInstance,
        (by exact inferInstanceAs (IsFinite r))⟩
    let R := FiniteEtale.pullback z
    let f₀ : R.obj P ⟶ R.obj Q := ObjectProperty.homMk
      (MorphismProperty.Over.homMk e₀.hom he₀)
    have hinv : e₀.inv ≫ pullback.snd p z = pullback.snd r z := by
      rw [← he₀, e₀.inv_hom_id_assoc]
    let g₀ : R.obj Q ⟶ R.obj P := ObjectProperty.homMk
      (MorphismProperty.Over.homMk e₀.inv hinv)
    obtain ⟨f, hf⟩ := (hfull P Q).2 f₀
    obtain ⟨g, hg⟩ := (hfull Q P).2 g₀
    have hfg : f ≫ g = 𝟙 P := (hfull P P).1 (by
      rw [R.map_comp, hf, hg, R.map_id]
      apply FiniteEtale.hom_ext
      exact e₀.hom_inv_id)
    have hgf : g ≫ f = 𝟙 Q := (hfull Q Q).1 (by
      rw [R.map_comp, hg, hf, R.map_id]
      apply FiniteEtale.hom_ext
      exact e₀.inv_hom_id)
    refine ⟨⟨f.hom.left, g.hom.left, ?_, ?_⟩, FiniteEtale.hom_left_comp f⟩
    · exact congrArg (fun k : P ⟶ P ↦ k.hom.left) hfg
    · exact congrArg (fun k : Q ⟶ Q ↦ k.hom.left) hgf

end AlgebraicGeometry.Scheme
