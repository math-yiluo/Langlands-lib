/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Graphs commute with change of base

Source: Mathlib IsPullback.mk' and IsPullback.of_right, and
IsOpenImmersion.range_pullbackSnd; corrected finite-étale lifting steps 1–3.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The product and graph squares after change of base are cartesian on schemes
and on graph images.
Source: corrected blueprint finite-étale lifting, steps 1–3; Stacks Tag 0GS2.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof: The product after base change represents triples consisting of a point of each
factor and a common point of the new base. Its map to the old product, together with
its new structure map, therefore has the universal property of the base change of
the old product. This proves the displayed cartesian square. For a morphism a, the
base change of its graph section is the graph of its base-changed morphism, since
both composites with the two projections agree. The graph is an open immersion
because q is étale and separated. The base change of an open immersion is the
restriction to the inverse image of its open image, so the graph images obey the
stated inverse-image identity. All these universal properties include empty schemes. -/
theorem Scheme.finiteEtale_graph_base_change
    {Y Y₀ U V : Scheme.{u}} (p : U ⟶ Y) (q : V ⟶ Y) [IsFinite q] [Etale q]
    (i : Y₀ ⟶ Y) :
    let p₀ := pullback.snd p i
    let q₀ := pullback.snd q i
    let j := pullback.map q₀ p₀ q p (pullback.fst q i) (pullback.fst p i) i
      (pullback.condition (f := q) (g := i)).symm (pullback.condition (f := p) (g := i)).symm
    IsPullback j (pullback.snd q₀ p₀) (pullback.snd q p) (pullback.fst p i) ∧
      ∀ a : U ⟶ V, ∀ ha : a ≫ q = p,
        let a₀ : pullback p i ⟶ pullback q i := pullback.lift (pullback.fst p i ≫ a) p₀
          (by dsimp [p₀]; simp [Category.assoc, ha, pullback.condition])
        Set.range (pullback.lift a₀ (𝟙 _) (by dsimp [a₀, q₀]; simp)).base =
          j.base ⁻¹' Set.range (pullback.lift a (𝟙 _) (by simpa using ha)).base  := by
  dsimp only
  let p₀ := pullback.snd p i
  let q₀ := pullback.snd q i
  let j := pullback.map q₀ p₀ q p (pullback.fst q i) (pullback.fst p i) i
    (pullback.condition (f := q) (g := i)).symm
    (pullback.condition (f := p) (g := i)).symm
  have hprod : IsPullback j (pullback.snd q₀ p₀) (pullback.snd q p)
      (pullback.fst p i) := by
    apply IsPullback.mk'
    · simp [j]
    · intro T m n h₁ h₂
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simpa [j] using congrArg (fun z ↦ z ≫ pullback.fst q p) h₁
        · change m ≫ pullback.fst q₀ p₀ ≫ q₀ = n ≫ pullback.fst q₀ p₀ ≫ q₀
          simpa only [Category.assoc, pullback.condition] using
            congrArg (fun z ↦ z ≫ p₀) h₂
      · exact h₂
    · intro T a b hab
      let c : T ⟶ pullback q i := pullback.lift (a ≫ pullback.fst q p) (b ≫ p₀)
        (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, hab]
          simp [p₀, Category.assoc, pullback.condition])
      let l : T ⟶ pullback q₀ p₀ := pullback.lift c b (by simp [c, q₀])
      refine ⟨l, ?_, ?_⟩
      · apply pullback.hom_ext <;> simp [l, j, c, hab]
      · simp [l]
  refine ⟨hprod, ?_⟩
  intro a ha
  let a₀ : pullback p i ⟶ pullback q i := pullback.lift (pullback.fst p i ≫ a) p₀
    (by dsimp [p₀]; simp [Category.assoc, ha, pullback.condition])
  let s : U ⟶ pullback q p := pullback.lift a (𝟙 U) (by simpa using ha)
  let s₀ : pullback p i ⟶ pullback q₀ p₀ :=
    pullback.lift a₀ (𝟙 (pullback p i)) (by dsimp [a₀, q₀]; simp)
  have hs : s ≫ pullback.snd q p = 𝟙 U := by simp [s]
  have hs₀ : s₀ ≫ pullback.snd q₀ p₀ = 𝟙 (pullback p i) := by simp [s₀]
  have hsq : s₀ ≫ j = pullback.fst p i ≫ s := by
    apply pullback.hom_ext <;> simp [s₀, j, a₀, s]
  have houter : IsPullback (s₀ ≫ pullback.snd q₀ p₀) (pullback.fst p i)
      (pullback.fst p i) (s ≫ pullback.snd q p) := by
    rw [hs, hs₀]
    exact IsPullback.of_horiz_isIso (by simp)
  have hsg : IsPullback (pullback.fst p i) s₀ s j :=
    (houter.of_right hsq hprod.flip).flip
  have : Mono s := mono_of_mono_fac hs
  have : Etale (s ≫ pullback.snd q p) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp _ (pullback.snd q p)
  have : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono _
  change Set.range s₀.base = j.base ⁻¹' Set.range s.base
  rw [← hsg.isoPullback_hom_snd]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsg.isoPullback.hom.surjective, Set.image_univ]
  exact IsOpenImmersion.range_pullbackSnd s j

end AlgebraicGeometry
