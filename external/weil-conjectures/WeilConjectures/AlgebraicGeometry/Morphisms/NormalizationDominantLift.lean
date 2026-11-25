/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Lifting dominant maps through absolute normalization

## References

* Stacks Project, Tag 035Q, part (4)
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

private theorem generic_factor {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    ∃ m : Spec X.functionField ⟶ Spec Y.functionField,
      m ≫ Y.fromSpecFunctionField = X.fromSpecFunctionField ≫ f := by
  have hη : f (genericPoint X) = genericPoint Y := by
    refine ((genericPoint_spec Y).eq ?_).symm
    have h := (genericPoint_spec X).image f.continuous
    rwa [Set.image_univ, f.denseRange.closure_range] at h
  have key (x : X) (y : Y) (h : f x = y) :
      ∃ m : Spec (X.presheaf.stalk x) ⟶ Spec (Y.presheaf.stalk y),
        m ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
    subst y
    exact ⟨Spec.map (f.stalkMap x), Scheme.SpecMap_stalkMap_fromSpecStalk f⟩
  exact key _ _ hη

private theorem dominant_generic_hom (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    (m : Spec X.functionField ⟶ Spec Y.functionField) : IsDominant m := by
  have : Subsingleton (Spec Y.functionField) :=
    inferInstanceAs (Subsingleton (Spec (.of Y.functionField)))
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨y⟩ : Nonempty (Spec X.functionField) := inferInstance
  exact subset_closure ⟨y, Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem normalization_generic_iso (Z : Scheme.{u}) [IsIntegral Z] :
    ∃ e : Spec Z.functionField ≅ Spec Z.normalization.functionField,
      e.hom ≫ Z.normalization.fromSpecFunctionField = Z.fromSpecFunctionField.toNormalization := by
  have hself : Z.fromSpecOfAlgebraFunctionField Z.functionField = Z.fromSpecFunctionField := by
    simp [fromSpecOfAlgebraFunctionField]
  have key {T : Scheme.{u}} [IsIntegral T] (φ ψ : T ⟶ Z)
      [QuasiCompact φ] [QuasiSeparated φ] [QuasiCompact ψ] [QuasiSeparated ψ]
      (h : φ = ψ)
      (hφ : ∃ e : T ≅ Spec φ.normalization.functionField,
        e.hom ≫ φ.normalization.fromSpecFunctionField = φ.toNormalization) :
      ∃ e : T ≅ Spec ψ.normalization.functionField,
        e.hom ≫ ψ.normalization.fromSpecFunctionField = ψ.toNormalization := by
    subst h
    exact hφ
  exact key _ _ hself (Z.exists_iso_toNormalization_normalizationIn Z.functionField)

/-- A dominant map from a normal integral scheme has a unique dominant lift to normalization. -/
theorem existsUnique_lift_normalization_of_dominant {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (g : Y ⟶ Z) [IsDominant g] :
    ∃! f : Y ⟶ Z.normalization, f ≫ Z.fromNormalization = g ∧ IsDominant f := by
  obtain ⟨m, hm⟩ := generic_factor g
  let j := Y.fromSpecFunctionField
  have hn : IsIso Y.fromNormalization := by
    have := Y.isIso_fromNormalization_restrict ⊤ (fun y _ ↦ hY y)
    have : IsIso (⊤ : Y.Opens).ι := Y.topIso.isIso_hom
    have : IsIso (Y.fromNormalization ⁻¹ᵁ ⊤).ι := by
      simpa using Y.normalization.topIso.isIso_hom
    have : IsIso ((Y.fromNormalization ∣_ ⊤) ≫ (⊤ : Y.Opens).ι) := inferInstance
    rw [morphismRestrict_ι] at this
    exact (isIso_comp_left_iff _ _).mp this
  let a := m ≫ Z.fromSpecFunctionField.toNormalization
  have ha : a ≫ Z.fromNormalization = j ≫ g := by
    simp [a, hm, j, Hom.toNormalization_fromNormalization]
  let b := pullback.lift a j ha
  let q := pullback.snd Z.fromNormalization g
  have hb : j = b ≫ q := by simp [b, q]
  let d := j.normalizationDesc b q hb
  let s := inv Y.fromNormalization ≫ d
  have hs : s ≫ q = 𝟙 Y := by
    dsimp only [s, d]
    rw [Category.assoc, Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  let f := s ≫ pullback.fst Z.fromNormalization g
  have hf : f ≫ Z.fromNormalization = g := by
    dsimp only [f]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have hj : j.toNormalization = j ≫ inv Y.fromNormalization := by
    apply (cancel_mono Y.fromNormalization).mp
    simp [j, Hom.toNormalization_fromNormalization]
  have hjf : j ≫ f = a := by
    dsimp only [f, s]
    rw [← Category.assoc j, ← Category.assoc j, ← hj,
      Hom.toNormalization_normalizationDesc]
    simp [b]
  have : IsDominant m := dominant_generic_hom Y Z m
  have : IsDominant (j ≫ f) := hjf.symm ▸ inferInstanceAs (IsDominant a)
  have : IsDominant f := IsDominant.of_comp j f
  refine ⟨f, ⟨hf, inferInstance⟩, ?_⟩
  intro f' hf'
  have : IsDominant f' := hf'.2
  obtain ⟨m', hm'⟩ := generic_factor f'
  obtain ⟨e, he⟩ := normalization_generic_iso Z
  have heν : Z.normalization.fromSpecFunctionField ≫ Z.fromNormalization =
      e.inv ≫ Z.fromSpecFunctionField := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, he]
    simp [Hom.toNormalization_fromNormalization]
  have hm'e : m' ≫ e.inv = m := by
    apply (cancel_mono Z.fromSpecFunctionField).mp
    rw [Category.assoc, ← heν, ← Category.assoc, hm', Category.assoc,
      hf'.1, ← hm]
  have hjf' : j ≫ f' = a := by
    rw [← hm', show m' = m ≫ e.hom by
      rw [← hm'e]; simp, Category.assoc, he]
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  exact ext_of_isSchemeTheoreticallyDominant Z.fromNormalization (hf'.1.trans hf.symm)
    j (hjf'.trans hjf.symm)

end AlgebraicGeometry.Scheme
