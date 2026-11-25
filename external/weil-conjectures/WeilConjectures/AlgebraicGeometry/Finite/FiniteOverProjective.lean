/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso

/-! # Finite covers of projective schemes over affine opens

Source: blueprint, chap-Smooth-purity, sk-prop-sf-cbc, node
`proposition-proper-direct-image-finite-coefficients`, order 1601 (blueprint:
proposition-proper-direct-image-finite-coefficients). The conclusion uses the node's corrected
affine-local H-projective convention.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem finite_over_projective_embedding_affine {S T Y : Scheme.{u}} [IsAffine S]
    (p : T ⟶ S) [IsHProjective p] (h : Y ⟶ T) [IsFinite h] :
    ∃ (N : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); S)),
      IsClosedImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); S) ↘ S = h ≫ p := by
  classical
  obtain ⟨n, hn, j, hj, hjp⟩ := IsHProjective.exists_isClosedImmersion (f := p)
  obtain ⟨m, hm, k, hk, hkp⟩ :=
    ProjectiveSpace.exists_isClosedImmersion_of_isFinite p j hjp h
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    have : IsEmpty Y := ⟨fun y ↦ isEmptyElim (k y)⟩
    exact ⟨0, isInitialOfIsEmpty.to _, inferInstance, isInitialOfIsEmpty.hom_ext _ _⟩
  | inr hnonempty =>
    obtain ⟨N, e, he, _⟩ := ProjectiveSpace.exists_finite_index_iso m S
    exact ⟨N, k ≫ e.hom, inferInstance, by rw [Category.assoc, he, hkp]⟩

/-- Over each affine open of a Noetherian base, a finite cover of a projective scheme
admits a closed immersion into a finite-dimensional projective space over that open.
Source: blueprint, chap-Smooth-purity, sk-prop-sf-cbc, order 1601
(blueprint: proposition-proper-direct-image-finite-coefficients).

Proof plan:
1. Fix an affine open U. Restrict the closed projective embedding of T and the finite
   morphism h to U. Standard projective charts show that T_U is quasi-compact over U
   (def-pc-projective-morphism, def-weil-closed-immersion,
   def-nagata-projective-space-base-change, def-nagata-relative-projective-space,
   def-weil-finite-integral-morphism, def-weil-finite-type-morphism).
2. Projective and finite morphisms are proper, as is their composite. Consequently
   Y_U is quasi-compact and locally of finite type over U (lem-pc-projective-proper,
   lem-weil-pbc-finite-proper, lem-weil-pbc-proper-composition,
   def-weil-proper-morphism, def-weil-finite-type-morphism).
3. Pull back O(1) and its coordinate sections along Y_U to projective space. The module
   is invertible (def-pc-projective-space-twist, lem-weil-pbc-invertible-pullback-tensor).
4. The coordinate nonvanishing loci are the affine inverse images of the standard
   charts under the finite map. They cover Y_U, so the pulled-back module is ample
   (def-nagata-relative-projective-space, def-weil-closed-immersion,
   def-weil-finite-integral-morphism, lem-weil-pbc-invertible-pullback-tensor,
   def-weil-pbc-ample-invertible-module).
5. The affine-base ample immersion theorem gives an immersion into some P^N_U over U
   (lem-weil-pbc-ample-very-ample-immersion-affine-base).
6. Projective space is separated over U, so the immersion is proper and hence closed
   (lem-weil-pbc-projective-space-proj-separated, lem-weil-pbc-proper-to-separated,
   lem-weil-pbc-proper-immersion-closed). With quasi-compactness this is projectivity
   (def-pc-projective-morphism). For an affine base take U to be the whole base. -/
theorem finite_over_projective_affineLocally {S T Y : Scheme.{u}}
    [CompactSpace S] [IsLocallyNoetherian S] (p : T ⟶ S) [IsProjective p]
    (h : Y ⟶ T) [IsFinite h] :
    (∀ (U : S.Opens), IsAffineOpen U →
      (∃ (N : ℕ) (i : ((h ≫ p) ⁻¹ᵁ U).toScheme ⟶
          ℙ(ULift.{u} (Fin (N + 1)); U.toScheme)),
        IsClosedImmersion i ∧
          i ≫ ℙ(ULift.{u} (Fin (N + 1)); U.toScheme) ↘ U.toScheme = (h ≫ p) ∣_ U) ∧
      IsProjective ((h ≫ p) ∣_ U)) ∧
    (IsAffine S → IsProjective (h ≫ p)) := by
  have haff : ∀ {B C D : Scheme.{u}} [IsAffine B] (q : C ⟶ B) [IsHProjective q]
      (g : D ⟶ C) [IsFinite g], IsProjective (g ≫ q) := by
    intro B C D _ q _ g _
    obtain ⟨N, i, hi, hiq⟩ := finite_over_projective_embedding_affine q g
    have : IsHProjective (g ≫ q) := ⟨⟨ULift.{u} (Fin (N + 1)), inferInstance, i, hi, hiq⟩⟩
    exact IsHProjective.isProjective _
  constructor
  · intro U hU
    have : IsAffine U.toScheme := hU
    obtain ⟨n, hn, j, hj, hjp⟩ := IsHProjective.exists_isClosedImmersion (f := p)
    have hw : (p ∣_ U) ≫ U.ι = ((p ⁻¹ᵁ U).ι ≫ j) ≫ ℙ(n; S) ↘ S := by
      rw [morphismRestrict_ι, Category.assoc, hjp]
    let k := ProjectiveSpace.liftBaseChange (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ j) hw
    have : IsClosedImmersion k := by
      apply MorphismProperty.of_isPullback
        (ProjectiveSpace.isPullback_liftBaseChange (p ∣_ U)
          (show IsPullback (p ⁻¹ᵁ U).ι (p ∣_ U) (j ≫ ℙ(n; S) ↘ S) U.ι from
            hjp.symm ▸ (isPullback_morphismRestrict p U).flip) hw)
      infer_instance
    have : IsHProjective (p ∣_ U) :=
      ⟨⟨n, hn, k, inferInstance, ProjectiveSpace.liftBaseChange_over _ _ hw⟩⟩
    rw [morphismRestrict_comp]
    exact ⟨finite_over_projective_embedding_affine (p ∣_ U) (h ∣_ p ⁻¹ᵁ U),
      haff (p ∣_ U) (h ∣_ p ⁻¹ᵁ U)⟩
  · intro hS
    have : IsAffine S := hS
    exact haff p h

end AlgebraicGeometry
