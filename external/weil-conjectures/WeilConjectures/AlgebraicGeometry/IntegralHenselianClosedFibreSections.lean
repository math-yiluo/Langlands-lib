/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction to the residue-field fibre of an integral scheme over a henselian
local ring is injective on module sections.
Source: Stacks Tags 09XK and 0A0C, the henselian comparison in Tag 0EYP.

Proof: Integrality makes Z affine. Write Z = Spec B by its canonical global-section
presentation. The ring map A → B is integral. Set J = m_A B. Tag 09XK makes (B,J)
a henselian pair. Apply isIso_globalSectionsUpperStarMap_of_henselianRing to the
proper identity morphism of Spec B and J. Its fibre is Spec(B/J). The tensor-quotient
isomorphism identifies this with the fibre over A/m_A. Transport the comparison
through the affine presentation and the given Cartesian square. These section
isomorphisms respect the inverse-image adjunction unit, so the displayed restriction
is an isomorphism, in particular injective. For B = 0 all the schemes in question
are empty and the section module is zero; the same argument applies.
(blueprint: new-integral-henselian-closed-fibre-sections) -/
theorem integralHenselianClosedFibreSections_injective
    (Λ : Type (u + 1)) [CommRing Λ]
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {Z Z₀ : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsIntegralHom p]
    (i₀ : Z₀ ⟶ Z) (p₀ : Z₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (sq : IsPullback i₀ p₀ p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Injective (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F).hom := by
  have : IsAffine Z := isAffine_of_isAffineHom p
  let B := Γ(Z, ⊤)
  let φ : CommRingCat.of A ⟶ B := (Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop
  let : Algebra A B := φ.hom.toAlgebra
  have hint : IsIntegralHom p.steinFactorizationBase := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsIntegralHom) Z.toSpecΓ p.steinFactorizationBase).mp
    rw [Scheme.toSpecΓ_steinFactorizationBase]
    infer_instance
  have : Algebra.IsIntegral A B :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hint)
  let J := (IsLocalRing.maximalIdeal A).map φ.hom
  have : HenselianRing B J :=
    henselianRing_of_isIntegral A (IsLocalRing.maximalIdeal A) B
  let j : Spec (.of (B ⧸ J)) ⟶ Spec B :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let q : Spec (.of (B ⧸ J)) ⟶ Spec (.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap J φ.hom Ideal.le_comap_map))
  have hquot : IsPullback j q (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
    exact (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_quotient φ (IsLocalRing.maximalIdeal A))).flip
  have hsq : IsPullback (i₀ ≫ Z.isoSpec.hom) p₀ (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
    apply sq.of_iso (Iso.refl _) Z.isoSpec (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · change p ≫ 𝟙 _ = Z.toSpecΓ ≫ p.steinFactorizationBase
      simp
    · simp
  let e : Z₀ ≅ Spec (.of (B ⧸ J)) := hsq.isoPullback ≪≫ hquot.isoPullback.symm
  have he : e.hom ≫ j ≫ Z.isoSpec.inv = i₀ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hquot.isoPullback_inv_fst_assoc, hsq.isoPullback_hom_fst_assoc,
      Iso.hom_inv_id, Category.comp_id]
  let G := (Z.isoSpec.inv)^*[ModuleCat.{u + 1} Λ].obj F
  have hj : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) j G) := by
    apply isIso_globalSectionsUpperStarMap_of_henselianRing Λ J (𝟙 (Spec B)) j (𝟙 _)
    exact IsPullback.of_vert_isIso ⟨by simp [j]⟩
  have hje : IsIso
      (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (e.hom ≫ j) G) := by
    have hc : IsIso
        (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (e.hom ≫ j) G ≫
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) e.hom j).hom.app G)) := by
      rw [globalSectionsUpperStarMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) e.hom j (e.hom ≫ j) rfl).hom.app G))
  have hi : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F) := by
    rw [← he, ← Category.assoc]
    have hc : IsIso
        (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
            ((e.hom ≫ j) ≫ Z.isoSpec.inv) F ≫
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) (e.hom ≫ j) Z.isoSpec.inv).hom.app F)) := by
      rw [globalSectionsUpperStarMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) (e.hom ≫ j) Z.isoSpec.inv
          ((e.hom ≫ j) ≫ Z.isoSpec.inv) rfl).hom.app F))
  exact (ConcreteCategory.bijective_of_isIso
    (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F)).injective

end AlgebraicGeometry.Etale
