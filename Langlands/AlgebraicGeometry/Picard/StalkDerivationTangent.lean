import Langlands.AlgebraicGeometry.DerivationDualNumber
import Langlands.AlgebraicGeometry.Picard.StalkTangentEquiv

/-! # Actual rational tangent maps and actual point-stalk derivations -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.GeneralLinear.DualNumber

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Actual rational tangent scheme maps are equivalent to derivations on the
actual point stalk with the coefficient action through the rational augmentation. -/
def rationalStalkDerivationTangentEquiv (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
    Derivation K (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) K ≃
      {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X // IsTangentVectorAt p x t} := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  exact (derivationDualNumberEquiv (rationalStalkAugmentation p x hx)).trans
    (rationalStalkTangentEquiv p x hx)

@[simp]
lemma rationalStalkDerivationTangentEquiv_apply_val (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
    ∀ D, (rationalStalkDerivationTangentEquiv p x hx D).val =
      Spec.map (CommRingCat.ofHom
        (derivationDualNumberLift (rationalStalkAugmentation p x hx) D).toRingHom) ≫
          X.fromSpecStalk (x (IsLocalRing.closedPoint K)) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  intros
  rfl

/-- The zero derivation gives the constant tangent map at the specified point. -/
lemma rationalStalkDerivationTangentEquiv_zero (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
    (rationalStalkDerivationTangentEquiv p x hx 0).val = dualNumberProjection K ≫ x := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  rw [rationalStalkDerivationTangentEquiv_apply_val, derivationDualNumberLift_zero]
  change Spec.map (CommRingCat.ofHom (rationalStalkAugmentation p x hx).toRingHom ≫
    CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, rationalStalkAugmentation_spec_comp]
  rfl

/-- Multiplication of the actual stalk derivation by any field element is
precomposition of the actual tangent map by spectrum of epsilon scaling. -/
lemma rationalStalkDerivationTangentEquiv_smul (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
    ∀ c D, (rationalStalkDerivationTangentEquiv p x hx (c • D)).val =
      Spec.map (CommRingCat.ofHom (epsilonScale c).toRingHom) ≫
        (rationalStalkDerivationTangentEquiv p x hx D).val := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  intro c D
  rw [rationalStalkDerivationTangentEquiv_apply_val,
    rationalStalkDerivationTangentEquiv_apply_val, derivationDualNumberLift_smul]
  change Spec.map (CommRingCat.ofHom
      (derivationDualNumberLift (rationalStalkAugmentation p x hx) D).toRingHom ≫
      CommRingCat.ofHom (epsilonScale c).toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]

/-- A stalk derivation gives the constant tangent map precisely when it vanishes. -/
lemma rationalStalkDerivationTangentEquiv_eq_constant_iff
    (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
    ∀ D, (rationalStalkDerivationTangentEquiv p x hx D).val =
      dualNumberProjection K ≫ x ↔ D = 0 := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  intro D
  rw [← rationalStalkDerivationTangentEquiv_zero p x hx]
  constructor
  · intro h
    exact (rationalStalkDerivationTangentEquiv p x hx).injective (Subtype.ext h)
  · rintro rfl
    rfl

end Langlands.AlgebraicGeometry.Picard
