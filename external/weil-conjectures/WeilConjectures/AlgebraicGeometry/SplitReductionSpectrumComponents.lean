/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.Spec
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.SplitReductionFactorThickenings
import WeilConjectures.AlgebraicGeometry.ThickeningIntegral

/-!
# Components of an affine scheme with split reduction

Source: smooth purity blueprint, `lem-weil-pbc-finite-pushforward-generic-constructible`,
finite-algebra calculation.
(blueprint: lem-weil-pbc-split-reduction-spectrum-components).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem universalHomeomorphism_of_thickening
    {X Y T : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ T)
    [IsClosedImmersion i] [Surjective i] [IsUniversalHomeomorphism (i ≫ f)] :
    IsUniversalHomeomorphism f := by
  have hfInt : IsIntegralHom f :=
    (isIntegralHom_iff_of_thickenings (𝟙 T) i f (i ≫ f)
      ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩ (by simp)).mp
      inferInstance
  have hfSurj : Surjective f := Surjective.of_comp i f
  have hfInj : UniversallyInjective f := by
    constructor
    intro Y' T' a b f' h
    let i' := pullback.snd i a
    have hi' : Surjective i' := inferInstance
    have hh : IsPullback (i' ≫ f') (pullback.fst i a) b (i ≫ f) :=
      (IsPullback.of_hasPullback i a).flip.paste_horiz h
    have hc : UniversallyInjective (i' ≫ f') :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hh.flip inferInstance
    intro y₁ y₂ hy
    obtain ⟨x₁, rfl⟩ := i'.surjective y₁
    obtain ⟨x₂, rfl⟩ := i'.surjective y₂
    have hx : x₁ = x₂ := (i' ≫ f').injective hy
    exact congrArg i' hx
  exact {}

/-- Lift the factors of a product decomposition through a nilradical reduction.

Source: smooth purity blueprint, `lem-weil-pbc-finite-pushforward-generic-constructible`,
finite-algebra calculation. (blueprint: lem-weil-pbc-split-reduction-spectrum-components).
Proof: Identify the spectrum of the finite product with the coproduct of factor spectra,
transport it across the supplied algebra equivalence, and lift the resulting clopen pieces
through the surjective nilradical closed immersion. Restrict the immersion to each lifted
piece and use invariance of integrality under thickenings, surjectivity of the composite,
and cancellation of universal injectivity after arbitrary base change. -/
theorem spectrum_components_of_split_reduction
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra A (D j)]
    (hD : ∀ j, IsUniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap A (D j)))))
    (he : Nonempty ((R ⧸ _root_.nilradical R) ≃ₐ[A] (∀ j, D j))) :
    ∃ (W : Fin r → (Spec (.of R)).Opens),
      (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
      ∀ i, IsUniversalHomeomorphism
        ((W i).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨W, hcover, hdisj, hW⟩ :=
    exists_split_reduction_factor_thickenings A R r D he
  refine ⟨W, hcover, hdisj, ?_⟩
  intro i
  obtain ⟨a, haClosed, haSurj, ha⟩ := hW i
  have : IsClosedImmersion a := haClosed
  have : Surjective a := haSurj
  have : IsUniversalHomeomorphism
      (a ≫ (W i).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
    rw [ha]
    exact hD i
  exact universalHomeomorphism_of_thickening a
    ((W i).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))

end AlgebraicGeometry.Scheme
