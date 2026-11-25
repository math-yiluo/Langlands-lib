/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Blowup.Affine.BaseChangeSurjectivity
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!

# The blow-up of an extended ideal is a closed subscheme of the base change

Let `φ : A →+* B` be a ring homomorphism, `I ⊆ A` an ideal and `J = I·B` its extension.
The blow-up of `J` maps to the fibre product `Spec B ×_{Spec A} Bl_I(Spec A)` via its
structure morphism and the functoriality morphism `AlgebraicGeometry.AffineBlowup.hom`.
We show that this canonical morphism is a **closed immersion** (the affine core of
Stacks Project Tag 080E).

The proof is chart-local on the fibre product: over the standard chart of `Bl_I` at a
degree-one element `x`, the morphism restricts to the `Spec` of the canonical ring map
`B ⊗_A A[I/x] →+* B[J/φ(x)]`, which is surjective by
`AlgebraicGeometry.AffineBlowup.closure_range_awayAlgebraMap_union_range_awayMap`.

## Main results

- `AlgebraicGeometry.AffineBlowup.isClosedImmersion_pullbackLift`

## Blueprint

Part of `thm:nagata-strict-transform-is-blowup` (Stacks Project Tag 080E), affine case.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry.AffineBlowup

variable {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}

/-- Chart-local form of `AlgebraicGeometry.AffineBlowup.isClosedImmersion_pullbackLift`:
over the standard chart of `Bl_I(Spec A)` at a degree-one element `x` of the Rees algebra,
the canonical morphism to the base change is `Spec` of a surjective ring map. -/
private lemma isClosedImmersion_pullbackLift_restrict (φ : A →+* B) (h : I.map φ = J)
    (x : reesAlgebra I) (hx : x ∈ reesGrading I 1) :
    IsClosedImmersion
      ((pullback.lift (toSpec J) (hom φ h) (hom_toSpec φ h).symm :
          AffineBlowup J ⟶ pullback (Spec.map (CommRingCat.ofHom φ)) (toSpec I)) ∣_
        pullback.snd (Spec.map (CommRingCat.ofHom φ)) (toSpec I) ⁻¹ᵁ
          (chart I x hx).opensRange) := by
  set κ : pullback (Spec.map (CommRingCat.ofHom φ))
        (Spec.map (CommRingCat.ofHom (awayAlgebraMap I x))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) (toSpec I) :=
    pullback.map _ _ _ _ (𝟙 _) (chart I x hx) (𝟙 _) (by simp)
      (by simpa using (chart_toSpec I x hx).symm) with hκ
  have : IsOpenImmersion κ := by
    rw [hκ]
    infer_instance
  set Θ : Spec (.of (Away (reesGrading J) (reesGrading.hom φ h x))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ))
        (Spec.map (CommRingCat.ofHom (awayAlgebraMap I x))) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (awayAlgebraMap J (reesGrading.hom φ h x))))
      (Spec.map (CommRingCat.ofHom (Away.map (reesGrading.hom φ h) x)))
      (by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, awayMap_awayAlgebraMap φ h x]) with hΘ
  have hrange : κ.opensRange =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (toSpec I) ⁻¹ᵁ
        (chart I x hx).opensRange := by
    apply TopologicalSpace.Opens.ext
    simp [hκ, Scheme.Pullback.range_map]
  have hw : chart J (reesGrading.hom φ h x) ((reesGrading.hom φ h).map_mem hx) ≫
      pullback.lift (toSpec J) (hom φ h) (hom_toSpec φ h).symm = Θ ≫ κ := by
    refine pullback.hom_ext ?_ ?_
    · simp [hκ, hΘ, chart_toSpec]
    · simp only [hκ, hΘ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact chart_hom φ h x hx
  have hpre : (pullback.lift (toSpec J) (hom φ h) (hom_toSpec φ h).symm :
        AffineBlowup J ⟶ pullback (Spec.map (CommRingCat.ofHom φ)) (toSpec I)) ⁻¹ᵁ
      κ.opensRange =
      (chart J (reesGrading.hom φ h x) ((reesGrading.hom φ h).map_mem hx)).opensRange := by
    rw [hrange, ← Scheme.Hom.comp_preimage, pullback.lift_snd, opensRange_chart,
      opensRange_chart]
    exact Proj.map_preimage_basicOpen (reesGrading.hom φ h)
      (reesGrading.irrelevant_le_map_hom φ h) x
  rw [← hrange]
  refine (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictArrowIso _ Θ hw hpre)).mpr ?_
  rw [hΘ]
  exact isClosedImmersion_pullbackLift_spec φ (awayAlgebraMap I x)
    (awayAlgebraMap J (reesGrading.hom φ h x)) (Away.map (reesGrading.hom φ h) x)
    (awayMap_awayAlgebraMap φ h x).symm
    (closure_range_awayAlgebraMap_union_range_awayMap φ h x hx)

/-- **The blow-up of an extended ideal is a closed subscheme of the base-changed
blow-up**, affine case (Stacks Project Tag 080E; blueprint:
`thm:nagata-strict-transform-is-blowup`): for a ring homomorphism `φ : A →+* B` with
`I.map φ = J`, the canonical morphism
`Bl_J(Spec B) ⟶ Spec B ×_{Spec A} Bl_I(Spec A)`, whose components are the structure
morphism of the blow-up of `J` and the functoriality morphism
`AlgebraicGeometry.AffineBlowup.hom`, is a closed immersion. -/
theorem isClosedImmersion_pullbackLift (φ : A →+* B) (h : I.map φ = J) :
    IsClosedImmersion
      (pullback.lift (toSpec J) (hom φ h) (hom_toSpec φ h).symm :
        AffineBlowup J ⟶ pullback (Spec.map (CommRingCat.ofHom φ)) (toSpec I)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun a : I ↦ pullback.snd (Spec.map (CommRingCat.ofHom φ)) (toSpec I) ⁻¹ᵁ
      (chart I (reesX I (a : A) a.2) (reesX_mem I (a : A) a.2)).opensRange) ?_ fun a ↦ ?_
  · have hcov : (⨆ a : I, (chart I (reesX I (a : A) a.2) (reesX_mem I (a : A) a.2)).opensRange) =
        ⊤ := by
      simp_rw [opensRange_chart]
      exact iSup_basicOpen_reesX_eq_top I
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  · exact isClosedImmersion_pullbackLift_restrict φ h _ _

end AlgebraicGeometry.AffineBlowup
