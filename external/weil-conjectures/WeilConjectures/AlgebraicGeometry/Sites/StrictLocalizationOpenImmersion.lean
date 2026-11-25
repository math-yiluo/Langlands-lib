/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal

/-!

# Strict localization along an open immersion

For an open immersion `j : U ⟶ S` and a geometric point `s'` of `U`, the morphism
`strictLocalization s' ⟶ strictLocalization (s' ≫ j)` is an isomorphism
(`AlgebraicGeometry.Scheme.isIso_strictLocalizationMap_of_isOpenImmersion`): the strict
localization of `S` at `s' ≫ j` maps into the open `U`, since all its points specialize to the
closed point, and the universal property of the strict localization gives the inverse.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S U : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (j : U ⟶ S)
  [IsOpenImmersion j] (s' : Spec (.of Ω) ⟶ U)

/-- The strict localization at `s` maps into every open subset containing the image of `s`: its
points all specialize to the closed point. -/
lemma range_strictLocalizationToBase_subset {S : Scheme.{u}} (s : Spec (.of Ω) ⟶ S) (O : Set S)
    (hO : IsOpen O) (x₀ : Spec (.of Ω)) (hs : s.base x₀ ∈ O) :
    Set.range (strictLocalizationToBase s).base ⊆ O := by
  rintro _ ⟨x, rfl⟩
  have hsp : x ⤳ IsLocalRing.closedPoint (strictHenselization s) :=
    IsLocalRing.specializes_closedPoint x
  have hcl : (strictLocalizationToBase s).base
      (IsLocalRing.closedPoint (strictHenselization s)) ∈ O := by
    rw [← spec_map_strictHenselizationEval_apply s (IsLocalRing.closedPoint Ω),
      ← Scheme.Hom.comp_apply, spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
    exact Subsingleton.elim x₀ (IsLocalRing.closedPoint Ω) ▸ hs
  exact hO.stableUnderGeneralization (hsp.map (strictLocalizationToBase s).base.hom.continuous) hcl

lemma range_strictLocalizationToBase_subset_range_of_isOpenImmersion :
    Set.range (strictLocalizationToBase (s' ≫ j)).base ⊆ Set.range j.base := by
  rintro _ ⟨x, rfl⟩
  have hsp : x ⤳ IsLocalRing.closedPoint (strictHenselization (s' ≫ j)) :=
    IsLocalRing.specializes_closedPoint x
  have hcl : (strictLocalizationToBase (s' ≫ j)).base
      (IsLocalRing.closedPoint (strictHenselization (s' ≫ j))) ∈ Set.range j.base := by
    rw [← spec_map_strictHenselizationEval_apply (s' ≫ j) (IsLocalRing.closedPoint Ω),
      ← Scheme.Hom.comp_apply, spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  exact (j.isOpenEmbedding.isOpen_range.stableUnderGeneralization
    ((hsp.map (strictLocalizationToBase (s' ≫ j)).base.hom.continuous))) hcl

/-- **Strict localization along an open immersion** is an isomorphism. -/
theorem isIso_strictLocalizationMap_of_isOpenImmersion :
    IsIso (strictLocalizationMap j s') := by
  have h₀ := isStrictlyHenselianLocalRing_strictHenselization (s' ≫ j)
  have : IsStrictlyHenselianLocalRing
      ↑(Limits.colimit.cocone (strictHenselizationDiagram (s' ≫ j))).1 := h₀
  let a₀ := strictLocalizationToBase (s' ≫ j)
  let a : strictLocalization (s' ≫ j) ⟶ U :=
    IsOpenImmersion.lift j a₀ (range_strictLocalizationToBase_subset_range_of_isOpenImmersion j s')
  have ha : a ≫ j = a₀ := IsOpenImmersion.lift_fac _ _ _
  let p₀ := Spec.map (strictHenselizationEval (s' ≫ j))
  have hp₀ : p₀ ≫ a = s' := by
    rw [← cancel_mono j, Category.assoc, ha]
    exact spec_map_strictHenselizationEval_comp_strictLocalizationToBase (s' ≫ j)
  obtain ⟨k, hk, hpk⟩ := exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing s' a p₀
    (spec_map_strictHenselizationEval_apply _ _) hp₀
  refine ⟨k, ?_, ?_⟩
  · refine hom_strictLocalization_ext s' ?_ (Spec.map (strictHenselizationEval s'))
      (IsLocalRing.closedPoint Ω) (spec_map_strictHenselizationEval_apply _ _) ?_
    · rw [Category.assoc, hk, Category.id_comp, ← cancel_mono j, Category.assoc, ha]
      exact strictLocalizationMap_comp_strictLocalizationToBase j s'
    · rw [Category.comp_id, ← Category.assoc,
        spec_map_strictHenselizationEval_comp_strictLocalizationMap]
      exact hpk
  · refine hom_strictLocalization_ext (s' ≫ j) ?_ p₀ (IsLocalRing.closedPoint Ω)
      (spec_map_strictHenselizationEval_apply _ _) ?_
    · rw [Category.assoc, strictLocalizationMap_comp_strictLocalizationToBase,
        ← Category.assoc, hk, ha, Category.id_comp]
    · rw [Category.comp_id, ← Category.assoc, hpk,
        spec_map_strictHenselizationEval_comp_strictLocalizationMap]

end AlgebraicGeometry.Scheme
