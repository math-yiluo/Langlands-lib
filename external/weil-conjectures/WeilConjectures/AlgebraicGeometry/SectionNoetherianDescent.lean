/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Noetherian descent of a finitely presented morphism with a section

Source: Stacks Project, Tags 055P (first reduction), 01ZA and 01ZM.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A finitely presented morphism over an affine base, together with a section, descends
in a cartesian square to noetherian schemes.

Source: Stacks Project, Tag 055P, first reduction; Tags 01ZA and 01ZM.
Proof: express the affine base as the inverse limit of spectra of its finitely generated
Z-subalgebras. All stages are noetherian. Descend the finitely presented source to a
stage by 01ZM(1). Regard the composite of the section with the source projection as a
morphism over that stage. Apply morphism descent on the system of later stages to obtain
a map from a later base stage to the source model, over the original base stage. Lift
this map and the identity of the later base to the pullback of the source model. This
lift is a section by the second projection identity, and its base change is the given
section by the first projection identity and uniqueness in the pullback. The later source
is of finite presentation over the noetherian stage, hence is noetherian too. Pasting
and cancelling the model's pullback square gives the claimed cartesian square.

(blueprint: lem-sbc-affine-section-noetherian-descent) -/
theorem exists_noetherian_model_with_section {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    ∃ (X₀ S₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (σ₀ : S₀ ⟶ X₀)
      (a : X ⟶ X₀) (b : S ⟶ S₀),
      IsNoetherian X₀ ∧ IsNoetherian S₀ ∧ LocallyOfFinitePresentation f₀ ∧
      QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧ σ₀ ≫ f₀ = 𝟙 S₀ ∧
      IsPullback a f f₀ b ∧ σ ≫ a = b ≫ σ₀ := by
  classical
  let N := Scheme.NoetherianApproximation.ofIsAffine S
  obtain ⟨i, Y, q, hqfp, hqqc, hqqs, a, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (D := N.D) N.isLimit f
  let : LocallyOfFinitePresentation q := hqfp
  let : QuasiCompact q := hqqc
  let : QuasiSeparated q := hqqs
  let D := Over.forget i ⋙ N.D
  have : ∀ {j k : Over i} (v : j ⟶ k), IsAffineHom (D.map v) := fun v ↦
    inferInstanceAs (IsAffineHom (N.D.map v.left))
  have : ∀ j : Over i, CompactSpace (D.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (N.D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace (D.obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (N.D.obj j.left))
  let c := (Cone.mk S N.π).whisker (Over.forget i)
  let t : D ⟶ (Functor.const (Over i)).obj (N.D.obj i) :=
    { app := fun j ↦ N.D.map j.hom
      naturality := fun j k v ↦ by
        change N.D.map v.left ≫ N.D.map k.hom = N.D.map j.hom ≫ 𝟙 _
        rw [← N.D.map_comp, Over.w v, Category.comp_id] }
  obtain ⟨j, τ, hτ, hτq⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t q c
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Cone.mk S N.π)).symm
        N.isLimit) (σ ≫ a) (by
        ext j
        change N.π.app j.left ≫ N.D.map j.hom = (σ ≫ a) ≫ q
        rw [Category.assoc, H.w, ← Category.assoc, hσ, Category.id_comp]
        exact (Cone.mk S N.π).w j.hom)
  change N.π.app j.left ≫ τ = σ ≫ a at hτ
  change τ ≫ q = N.D.map j.hom at hτq
  let X₀ := pullback q (N.D.map j.hom)
  let f₀ : X₀ ⟶ N.D.obj j.left := pullback.snd _ _
  let σ₀ : N.D.obj j.left ⟶ X₀ := pullback.lift τ (𝟙 _) (by simp [hτq])
  let a₀ : X ⟶ X₀ := pullback.lift a (f ≫ N.π.app j.left) (by
    rw [H.w, Category.assoc, (Cone.mk S N.π).w j.hom])
  have Ha : IsPullback a₀ f f₀ (N.π.app j.left) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q (N.D.map j.hom))
    · simpa [a₀, (Cone.mk S N.π).w j.hom] using H
    · simp [a₀]
  have hsection : σ ≫ a₀ = N.π.app j.left ≫ σ₀ := by
    apply pullback.hom_ext
    · simpa [a₀, σ₀, Category.assoc] using hτ.symm
    · simp only [a₀, σ₀, Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, hσ, Category.id_comp]
  have : LocallyOfFinitePresentation f₀ := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.snd q (N.D.map j.hom)))
  have : QuasiCompact f₀ := inferInstanceAs (QuasiCompact (pullback.snd q (N.D.map j.hom)))
  have : QuasiSeparated f₀ := inferInstanceAs (QuasiSeparated (pullback.snd q (N.D.map j.hom)))
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  exact ⟨X₀, N.D.obj j.left, f₀, σ₀, a₀, N.π.app j.left, ⟨⟩,
    inferInstance, inferInstance, inferInstance, inferInstance, by simp [σ₀, f₀], Ha,
    hsection⟩

end AlgebraicGeometry
