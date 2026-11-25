/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierRootGeometry
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedProjectorCoverIso
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierCoefficientPull

/-! # Root-normalized negation of Artin–Schreier sheaves

Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, Duality,
the negating-roots construction (blueprint: lem-wft-as-root-negation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierUnit

attribute [local irreducible] AffineSpace.neg AffineSpace.homOfVector
  AffineSpace.artinSchreierMap Etale.artinSchreierScaling


open ArtinSchreierTrace

variable (k : Type u) [Field k] [Fintype k]
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [Fintype k] in
private theorem neg_eq_scaling :
    AffineSpace.neg PUnit (Spec (.of k)) = Etale.artinSchreierScaling k (-1) := by
  unfold Etale.artinSchreierScaling
  rw [map_neg, map_one, AffineSpace.smul_neg_one]

/-- Negation commutes with the universal Artin–Schreier map. -/
theorem neg_comp_universalCover :
    AffineSpace.neg PUnit (Spec (.of k)) ≫ (universalCover k).hom =
      (universalCover k).hom ≫ AffineSpace.neg PUnit (Spec (.of k)) := by
  rw [neg_eq_scaling]
  exact Etale.artinSchreierScaling_comp_artinSchreierMap (-1 : k)

/-- The universal cover composed with negation on its base. -/
def negativeCover : Over (AffineSpace PUnit (Spec (.of k))) :=
  Over.mk ((universalCover k).hom ≫ AffineSpace.neg PUnit (Spec (.of k)))

/-- Negation of the covering coordinate, over the original affine-line base. -/
def negativeCoverIso : universalCover k ≅ negativeCover k :=
  Over.isoMk
    { hom := AffineSpace.neg PUnit (Spec (.of k))
      inv := AffineSpace.neg PUnit (Spec (.of k))
      hom_inv_id := AffineSpace.neg_comp_neg _ _
      inv_hom_id := AffineSpace.neg_comp_neg _ _ } (by
    change AffineSpace.neg PUnit (Spec (.of k)) ≫
      ((universalCover k).hom ≫ AffineSpace.neg PUnit (Spec (.of k))) =
        (universalCover k).hom
    rw [← Category.assoc, neg_comp_universalCover, Category.assoc,
      AffineSpace.neg_comp_neg, Category.comp_id])

/-- The specified translation automorphism of the universal cover. -/
def universalTranslation (c : k) : universalCover k ⟶ universalCover k :=
  Over.homMk (Etale.artinSchreierTranslation k c)
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)

/-- The averaging endomorphism of the universal cover's coefficient functions for the
character `χ`, built from the universal translations. -/
abbrev universalProjector (χ : AddChar k (MonObj.Γ Λ)) :=
  condensedProjector Λ k (universalCover k) (universalTranslation k) χ

/-- Translation remains a cover map after negation on the base. -/
def negativeTranslation (c : k) : negativeCover k ⟶ negativeCover k :=
  Over.homMk (Etale.artinSchreierTranslation k c) (by
    dsimp only [negativeCover, Over.mk_hom]
    rw [← Category.assoc, Etale.artinSchreierTranslation_comp_artinSchreierMap])

private theorem negativeCoverIso_translation (c : k) :
    universalTranslation k c ≫ (negativeCoverIso k).hom =
      (negativeCoverIso k).hom ≫ negativeTranslation k (-c) := by
  apply Over.OverMorphism.ext
  change Etale.artinSchreierTranslation k c ≫ AffineSpace.neg PUnit (Spec (.of k)) =
    AffineSpace.neg PUnit (Spec (.of k)) ≫ Etale.artinSchreierTranslation k (-c)
  rw [neg_eq_scaling]
  simpa only [neg_one_mul] using
    Etale.artinSchreierTranslation_comp_artinSchreierScaling c (-1)

/-- Negating the indexing action is the inverse-character projector. -/
theorem condensedProjector_neg_action
    {T : Scheme.{u}} (Y : Over T) (σ : k → (Y ⟶ Y))
    (χ : AddChar k (MonObj.Γ Λ)) :
    condensedProjector Λ k Y (fun c ↦ σ (-c)) χ =
      condensedProjector Λ k Y σ χ⁻¹ := by
  classical
  unfold condensedProjector
  apply Fintype.sum_equiv (Equiv.neg k)
  intro c
  simp only [Equiv.neg_apply, AddChar.inv_apply, neg_neg]

/-- The universal averaging endomorphism is an actual idempotent. -/
theorem universalProjector_idempotent (χ : AddChar k (MonObj.Γ Λ))
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ)) :
    (universalProjector k Λ χ).asHom ≫ (universalProjector k Λ χ).asHom =
      (universalProjector k Λ χ).asHom := by
  apply condensedProjector_idempotent Λ k (universalCover k) (universalTranslation k) _ χ hq
  intro a b
  apply Over.OverMorphism.ext
  exact Etale.artinSchreierTranslation_add k a b

/-- The specified universal image has its canonical idempotent retraction. -/
theorem universalProjector_image_retraction (χ : AddChar k (MonObj.Γ Λ))
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ)) :
    image.ι (universalProjector k Λ χ).asHom ≫
        factorThruImage (universalProjector k Λ χ).asHom =
      𝟙 _ := by
  rw [← cancel_mono (image.ι _), ← cancel_epi (factorThruImage _)]
  simp only [Category.assoc, image.fac_assoc, image.fac, Category.id_comp]
  exact universalProjector_idempotent k Λ χ hq

/-- Negation transports the two projector images and the actual root evaluations.
The remaining comparison with pullback along base negation is separate from this
isomorphism of covers. Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md,
Duality, negating roots (blueprint: lem-wft-as-root-negation). -/
theorem rootNegation_coverComparison (χ : AddChar k (MonObj.Γ Λ)) :
    ∃ J : image (universalProjector k Λ χ).asHom ≅
        image (condensedProjector Λ k (negativeCover k) (negativeTranslation k) χ⁻¹).asHom,
      ∀ (T : Scheme.{u}) (x : T ⟶ AffineSpace PUnit (Spec (.of k)))
        (s : Over.mk x ⟶ negativeCover k),
        (ProEtale.CondensedRing.upperStar Λ x).map J.hom ≫
            condensedEvaluation Λ x s
              (image.ι (condensedProjector Λ k (negativeCover k)
                (negativeTranslation k) χ⁻¹).asHom) =
          condensedEvaluation Λ x (s ≫ (negativeCoverIso k).inv)
            (image.ι (universalProjector k Λ χ).asHom) := by
  rw [← condensedProjector_neg_action k Λ (negativeCover k) (negativeTranslation k) χ]
  obtain ⟨J, hJ⟩ := condensedProjector_coverIso Λ k (negativeCoverIso k)
    (universalTranslation k) (fun c ↦ negativeTranslation k (-c))
    (negativeCoverIso_translation k) χ
  refine ⟨J, ?_⟩
  have hid : (Iso.refl (image (universalProjector k Λ χ).asHom)).hom ≫
        image.ι (universalProjector k Λ χ).asHom =
      image.ι (universalProjector k Λ χ).asHom ≫ condensedPull Λ (𝟙 (universalCover k)) := by
    rw [condensedPull_id, Category.comp_id, Iso.refl_hom, Category.id_comp]
  have he := (hJ (universalCover k) (𝟙 _) _
    (image.ι (universalProjector k Λ χ).asHom) (Iso.refl _) hid).2
  intro T x s
  simpa only [Iso.refl_trans, Category.comp_id] using he T x s

/-- Pullback along negation is self-inverse by its specified composition comparisons. -/
def negationPullEquivalence :
    Mod (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit (Spec (.of k)))) Ab.{u + 1})
        (ProEtale.condensedRingObj Λ (AffineSpace PUnit (Spec (.of k)))) ≌
      Mod (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit (Spec (.of k)))) Ab.{u + 1})
        (ProEtale.condensedRingObj Λ (AffineSpace PUnit (Spec (.of k)))) :=
  CategoryTheory.Equivalence.mk
    (ProEtale.CondensedRing.upperStar Λ (AffineSpace.neg PUnit (Spec (.of k))))
    (ProEtale.CondensedRing.upperStar Λ (AffineSpace.neg PUnit (Spec (.of k))))
    ((ProEtale.CondensedRing.upperStarId Λ _).symm ≪≫
      ProEtale.CondensedRing.upperStarCongr Λ (AffineSpace.neg_comp_neg _ _).symm ≪≫
        ProEtale.CondensedRing.upperStarComp Λ _ _)
    ((ProEtale.CondensedRing.upperStarComp Λ _ _).symm ≪≫
      ProEtale.CondensedRing.upperStarCongr Λ (AffineSpace.neg_comp_neg _ _) ≪≫
        ProEtale.CondensedRing.upperStarId Λ _)

/-- The two right adjoints of negation pullback have their canonical comparison. -/
def negationPullLowerStarIso :
    ProEtale.CondensedRing.upperStar Λ (AffineSpace.neg PUnit (Spec (.of k))) ≅
      ProEtale.CondensedRing.lowerStar Λ (AffineSpace.neg PUnit (Spec (.of k))) :=
  Adjunction.rightAdjointUniq (negationPullEquivalence k Λ).toAdjunction
    (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ
      (AffineSpace.neg PUnit (Spec (.of k))))

omit [Fintype k] in
/-- The adjoint comparison is compatible with the actual coefficient counit. -/
theorem negationPullLowerStarIso_counit
    (M : Mod (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit (Spec (.of k)))) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ (AffineSpace PUnit (Spec (.of k))))) :
    (ProEtale.CondensedRing.upperStar Λ (AffineSpace.neg PUnit (Spec (.of k)))).map
        ((negationPullLowerStarIso k Λ).hom.app M) ≫
      (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ
        (AffineSpace.neg PUnit (Spec (.of k)))).counit.app M =
      (negationPullEquivalence k Λ).toAdjunction.counit.app M := by
  exact Adjunction.rightAdjointUniq_hom_app_counit
    (negationPullEquivalence k Λ).toAdjunction
    (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ
      (AffineSpace.neg PUnit (Spec (.of k)))) M

/-- Pulling base negation back along a function gives the recorded negative-function sheaf.
This uses only the specified composition and equality-transport comparisons. -/
def negativeFunctionIso (χ : AddChar k (MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    (ProEtale.CondensedRing.upperStar Λ
        (AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ f))).obj
      ((ProEtale.CondensedRing.upperStar Λ (AffineSpace.neg PUnit (Spec (.of k)))).obj
        (image (universalProjector k Λ χ).asHom)) ≅ condensedSheafOf Λ k χ X (-f) := by
  unfold condensedSheafOf
  exact (ProEtale.CondensedRing.upperStarComp Λ
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ f))
      (AffineSpace.neg PUnit (Spec (.of k)))).symm.app (image (universalProjector k Λ χ).asHom) ≪≫
    (ProEtale.CondensedRing.upperStarCongr Λ (functionMap_neg k X f).symm).app _

end AlgebraicGeometry.ArtinSchreierUnit
