/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.FieldTheory.Galois.Basic

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.Mathlib.AlgebraicGeometry.Limits

/-! # The Galois group of one field component of a finite torsor

## References

* Stacks Project, Tags 03SF and 03QR
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The torsor action relates two maps from a nonempty single-point scheme uniquely. -/
private theorem torsor_translation_unique
    {G : Type (u + 1)} [Group G] [Finite G] {Y X : Scheme.{u}}
    (T : GaloisCover G Y) [Subsingleton X] [Nonempty X]
    (x y : X ⟶ T.P) (h : y ≫ T.π = x ≫ T.π) :
    ∃! g : G, x ≫ T.smul g = y := by
  let D := Sigma.desc fun g : G ↦
    pullback.lift (f := T.π) (g := T.π) (T.smul g) (𝟙 T.P)
      (by simp [T.smul_π])
  let : IsIso D := T.isIso_sigmaDesc
  let z := pullback.lift y x h
  obtain ⟨g, w, hw⟩ := exists_comp_sigmaι_eq_of_subsingleton (z ≫ inv D)
  have hw' : w ≫ pullback.lift (f := T.π) (g := T.π) (T.smul g) (𝟙 T.P)
      (by simp [T.smul_π]) = z := by
    rw [← Sigma.ι_comp_desc (fun g : G ↦
      pullback.lift (f := T.π) (g := T.π) (T.smul g) (𝟙 T.P)
        (by simp [T.smul_π])) g, ← Category.assoc, hw]
    simp [D]
  have hx : w = x := by
    have he := congrArg (fun f ↦ f ≫ pullback.snd T.π T.π) hw'
    simpa [z] using he
  have hg : x ≫ T.smul g = y := by
    have he := congrArg (fun f ↦ f ≫ pullback.fst T.π T.π) hw'
    simpa [z, hx] using he
  refine ⟨g, hg, ?_⟩
  intro k hk
  have he : x ≫ Sigma.ι (fun _ : G ↦ T.P) k =
      x ≫ Sigma.ι (fun _ : G ↦ T.P) g := by
    apply (cancel_mono D).mp
    simp only [Category.assoc, D, Sigma.ι_comp_desc]
    ext <;> simp [hk, hg]
  obtain ⟨a⟩ := ‹Nonempty X›
  have ha := congrArg (fun f : X ⟶ ∐ fun _ : G ↦ T.P ↦ f.base a) he
  simp only [Scheme.Hom.comp_apply] at ha
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp ha)

/-- Two embeddings of a field component into one field differ by an endomorphism. -/
private theorem component_embedding_factors
    (K : Type u) [Field K] (G : Type (u + 1)) [Group G] [Finite G]
    (T : GaloisCover G (Spec (CommRingCat.of K)))
    (E L : Type u) [Field E] [Field L] [Algebra K E] [Algebra K L]
    (j : Spec (CommRingCat.of E) ⟶ T.P) [IsOpenImmersion j]
    (hj : j ≫ T.π = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (σ τ : E →ₐ[K] L) : ∃ a : E →ₐ[K] E, σ.comp a = τ := by
  let x := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let y := Spec.map (CommRingCat.ofHom τ.toRingHom)
  have hbase : (y ≫ j) ≫ T.π = (x ≫ j) ≫ T.π := by
    dsimp [x, y]
    simp only [Category.assoc, hj, ← Spec.map_comp]
    congr 1
    ext r
    exact (τ.commutes r).trans (σ.commutes r).symm
  obtain ⟨g, hg, _⟩ := torsor_translation_unique T (x ≫ j) (y ≫ j) hbase
  have hr : Set.range (j ≫ T.smul g).base ⊆ Set.range j.base := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of L)))
    refine ⟨y q, ?_⟩
    have he := congrArg (fun f ↦ f.base q) hg
    simpa only [Scheme.Hom.comp_apply, Subsingleton.elim (x q) p] using he.symm
  let f := IsOpenImmersion.lift j (j ≫ T.smul g) hr
  have hf : f ≫ j = j ≫ T.smul g := IsOpenImmersion.lift_fac _ _ _
  have hfK : f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
    rw [← hj, ← Category.assoc, hf, Category.assoc, T.smul_π]
  let r := Spec.preimage f
  have hrK : ∀ k : K, r.hom (algebraMap K E k) = algebraMap K E k := by
    rw [← Spec.map_preimage f, ← Spec.map_comp] at hfK
    exact fun k ↦ congrArg (fun φ ↦ φ.hom k) (Spec.map_injective hfK)
  let a : E →ₐ[K] E := { r.hom with commutes' := hrK }
  refine ⟨a, ?_⟩
  have he : x ≫ f = y := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hf]
    exact hg
  apply AlgHom.ext
  intro t
  rw [← Spec.map_preimage f, ← Spec.map_comp] at he
  exact congrArg (fun φ ↦ φ.hom t) (Spec.map_injective he)

/-- A field component of a finite group torsor is Galois, with automorphism group isomorphic
 to a subgroup of the torsor group. -/
theorem field_torsor_component_galois_group
    (K : Type u) [Field K]
    (G : Type (u + 1)) [Group G] [Finite G]
    (T : GaloisCover G (Spec (CommRingCat.of K)))
    (E : Type u) [Field E] [Algebra K E]
    (j : Spec (CommRingCat.of E) ⟶ T.P) [IsOpenImmersion j]
    (hj : j ≫ T.π = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    IsGalois K E ∧ ∃ H : Subgroup G, Nonempty ((E ≃ₐ[K] E) ≃* H) := by
  classical
  let := T.etale
  have het : Etale (Spec.map (CommRingCat.ofHom (algebraMap K E))) := by
    rw [← hj]
    infer_instance
  have hetA : Algebra.Etale K E :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp het)
  let := hetA
  have hsep : Algebra.IsSeparable K E := Algebra.FormallyUnramified.isSeparable K E
  let : FiniteDimensional K E := Algebra.FormallyUnramified.finite_of_free K E
  -- All embeddings land in one field range, so this range is its own normal closure.
  let L := AlgebraicClosure K
  let σ : E →ₐ[K] L := IsAlgClosed.lift
  have hn : IntermediateField.normalClosure K E L = σ.fieldRange := by
    apply le_antisymm
    · apply normalClosure_le_iff.mpr
      intro τ
      obtain ⟨a, ha⟩ := component_embedding_factors K G T E L j hj σ τ
      rintro t ⟨x, hx⟩
      refine ⟨a x, ?_⟩
      exact (DFunLike.congr_fun ha x).trans hx
    · exact σ.fieldRange_le_normalClosure
  have hnσ : Normal K σ.fieldRange := by
    rw [← hn]
    infer_instance
  have hnE : Normal K E := Normal.of_algEquiv σ.equivFieldRange.symm
  refine ⟨isGalois_iff.mpr ⟨hsep, hnE⟩, ?_⟩
  -- Using inverse automorphisms compensates for the contravariance of Spec.
  have hc : ∀ a : E ≃ₐ[K] E, ∃! g : G,
      j ≫ T.smul g = Spec.map (CommRingCat.ofHom a.symm.toRingHom) ≫ j := by
    intro a
    apply torsor_translation_unique
    simp only [Category.assoc, hj, ← Spec.map_comp]
    congr 1
    ext k
    exact a.symm.commutes k
  let c : (E ≃ₐ[K] E) → G := fun a ↦ (hc a).exists.choose
  have hcm : ∀ a : E ≃ₐ[K] E,
      j ≫ T.smul (c a) = Spec.map (CommRingCat.ofHom a.symm.toRingHom) ≫ j :=
    fun a ↦ (hc a).exists.choose_spec
  have hcu : ∀ (a : E ≃ₐ[K] E) (g : G),
      j ≫ T.smul g = Spec.map (CommRingCat.ofHom a.symm.toRingHom) ≫ j → g = c a := by
    intro a g hg
    exact (hc a).unique hg (hcm a)
  let ρ : (E ≃ₐ[K] E) →* G := {
    toFun := c
    map_one' := by
      apply (hcu 1 1 ?_).symm
      simp only [T.one_smul, Category.comp_id]
      change j = Spec.map (𝟙 (CommRingCat.of E)) ≫ j
      simp
    map_mul' := by
      intro a b
      apply (hcu (a * b) (c a * c b) ?_).symm
      rw [T.mul_smul, ← Category.assoc, hcm b, Category.assoc, hcm a,
        ← Category.assoc, ← Spec.map_comp]
      congr 2 }
  have hρ : Function.Injective ρ := by
    intro a b hab
    have he : Spec.map (CommRingCat.ofHom a.symm.toRingHom) =
        Spec.map (CommRingCat.ofHom b.symm.toRingHom) := by
      apply (cancel_mono j).mp
      rw [← hcm a, ← hcm b]
      exact congrArg (fun g ↦ j ≫ T.smul g) hab
    apply inv_injective
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun φ ↦ φ.hom x) (Spec.map_injective he)
  exact ⟨ρ.range, ⟨MonoidHom.ofInjective hρ⟩⟩

end AlgebraicGeometry.Scheme
