import Langlands.AlgebraicGeometry.AdicAffinePoints
import Langlands.AlgebraicGeometry.AffineQuotientPullback

/-! # Base change of spectra of adic quotients -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The map on adic quotients induced by a ring homomorphism. -/
def quotientRingMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ (n + 1) →+* B ⧸ (I.map φ) ^ (n + 1) :=
  Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

/-- The map of affine quotient schemes induced by a ring homomorphism. -/
def quotientSpecMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    quotientSpec (I.map φ) n ⟶ quotientSpec I n :=
  Spec.map (CommRingCat.ofHom (quotientRingMap φ I n))

@[reassoc] theorem quotientSpecMap_quotientMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    quotientSpecMap φ I n ≫ quotientMap I n =
      quotientMap (I.map φ) n ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold quotientSpecMap quotientMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1

@[reassoc] theorem quotientSpecMap_transition (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    transition (I.map φ) n ≫ quotientSpecMap φ I (n + 1) =
      quotientSpecMap φ I n ≫ transition I n := by
  unfold quotientSpecMap transition
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  rfl

/-- Extended-ideal quotients form the actual Cartesian quotient square. -/
theorem isPullback_quotientSpecMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    IsPullback (quotientSpecMap φ I n) (quotientMap (I.map φ) n)
      (quotientMap I n) (Spec.map (CommRingCat.ofHom φ)) := by
  have hgen (J : Ideal B) (hJ : (I ^ (n + 1)).map φ = J) :
      IsPullback
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J φ
          (by rw [← hJ]; exact Ideal.le_comap_map))))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        (quotientMap I n) (Spec.map (CommRingCat.ofHom φ)) := by
    subst J
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (Langlands.AlgebraicGeometry.isPushout_quotient_map φ (I ^ (n + 1)))
  exact hgen _ (Ideal.map_pow _ _ _)

end Langlands.GroupScheme.HomScheme.Adic
