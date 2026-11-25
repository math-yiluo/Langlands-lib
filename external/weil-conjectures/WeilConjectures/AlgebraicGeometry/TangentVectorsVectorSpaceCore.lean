/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.DualNumberSchemePushout
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.FinCases

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-! Core pushout and gluing assertions for dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-core)

Proof in words: apply the dual-number scheme pushout theorem to the two
coordinate projections, then use the local-ring description of maps from
spectra to obtain existence and uniqueness of the glued morphism. The
compatibility with the structure morphism follows by uniqueness after
mapping to `Spec k`. -/
/-- Core pushout and gluing assertions for dual-number tangent vectors.
Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2.
(blueprint: lem-sc-tangent-vectors-core)

Proof in words: specialize `existsUnique_dualNumberScheme_extension` to two
copies. The equality of the two composites from the residue point follows
from the common constant-coordinate projection. Existence and uniqueness
of extensions into every scheme give the pushout universal property.
Tangent vectors have the same restriction to the residue point, so they
satisfy the gluing hypothesis. Finally, the two coordinate inclusions
followed by the structure map of the square-zero algebra give the structure
map of the dual numbers. The two given over-base equations therefore make
both restrictions of the glued structure map equal to those of the required
map; pushout hom-extensionality gives equality. -/
theorem tangentVectors_core
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    let K := X.residueField x
    let D := Spec (.of (DualNumber K))
    let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
    let b := X.fromSpecResidueField x
    let c : Spec K ⟶ D :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    let q : D ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
    let r : E ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K (Fin 2 → K)))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    IsPushout c c (j 0) (j 1) ∧
      (∀ θ₁ θ₂ : T, ∃! Θ : E ⟶ X, j 0 ≫ Θ = θ₁.val ∧ j 1 ≫ Θ = θ₂.val) ∧
      (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
        j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → Θ ≫ p = r ≫ b ≫ p) := by
  classical
  let K := X.residueField x
  let D := Spec (.of (DualNumber K))
  let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
  let b := X.fromSpecResidueField x
  let c : Spec K ⟶ D :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
  let q : D ⟶ Spec K :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
  let r : E ⟶ Spec K :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K (Fin 2 → K)))
  let j : Fin 2 → (D ⟶ E) := fun i =>
    Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
  let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
  change IsPushout c c (j 0) (j 1) ∧
    (∀ θ₁ θ₂ : T, ∃! Θ : E ⟶ X, j 0 ≫ Θ = θ₁.val ∧ j 1 ≫ Θ = θ₂.val) ∧
    (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
      j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → Θ ≫ p = r ≫ b ≫ p)
  have hext (Y : Scheme.{u}) (a a' : D ⟶ Y) (h : c ≫ a = c ≫ a') :
      ∃! f : E ⟶ Y, j 0 ≫ f = a ∧ j 1 ≫ f = a' := by
    let θ : Fin 2 → (D ⟶ Y) := Fin.cases a (fun _ => a')
    have hθ : ∀ i i' : Fin 2, c ≫ θ i = c ≫ θ i' := by
      intro i i'
      fin_cases i <;> fin_cases i'
      · rfl
      · exact h
      · exact h.symm
      · rfl
    obtain ⟨f, hf, huniq⟩ :=
      existsUnique_dualNumberScheme_extension K 2 (by decide) Y θ hθ
    refine ⟨f, ⟨hf 0, hf 1⟩, ?_⟩
    intro g hg
    apply huniq g
    intro i
    fin_cases i
    · exact hg.1
    · exact hg.2
  have hw : c ≫ j 0 = c ≫ j 1 := by
    dsimp [c, j]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hp : IsPushout c c (j 0) (j 1) := by
    apply IsPushout.mk' hw
    · intro Y f g h₀ h₁
      obtain ⟨l, hl, huniq⟩ := hext Y (j 0 ≫ f) (j 1 ≫ f)
        (by rw [← Category.assoc, ← Category.assoc, hw])
      exact (huniq f ⟨rfl, rfl⟩).trans (huniq g ⟨h₀.symm, h₁.symm⟩).symm
    · intro Y a a' h
      exact (hext Y a a' h).exists
  refine ⟨hp, ?_, ?_⟩
  · intro θ₁ θ₂
    exact hext X θ₁.val θ₂.val (θ₁.property.1.trans θ₂.property.1.symm)
  · intro θ₁ θ₂ Θ h₀ h₁
    have hjq (i : Fin 2) : j i ≫ r = q := by
      dsimp [j, r, q]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      apply TrivSqZeroExt.ext <;> simp
    apply hp.hom_ext
    · rw [← Category.assoc, h₀, θ₁.property.2, ← Category.assoc, ← Category.assoc,
        hjq, Category.assoc]
    · rw [← Category.assoc, h₁, θ₂.property.2, ← Category.assoc, ← Category.assoc,
        hjq, Category.assoc]

end AlgebraicGeometry
