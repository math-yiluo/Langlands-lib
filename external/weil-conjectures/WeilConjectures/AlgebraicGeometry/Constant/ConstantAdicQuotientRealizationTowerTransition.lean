/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-! # Pullback of the consecutive adic tower transition

This is the tower-normalization substep of the consecutive quotient
realization argument.  It contains no constant realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

private noncomputable def pullbackScalarIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedExtend φ ⋙ adicTowerPullback g S ≅
      adicTowerPullback g R ⋙ pbcDerivedExtend ((adicTowerInverseImage g).map φ) := by
  let R' := (adicTowerInverseImage g).obj R
  let S' := (adicTowerInverseImage g).obj S
  let φ' := (adicTowerInverseImage g).map φ
  let adjR := (proEtaleRingDerivedOperations_adjunction g R R' (Iso.refl _)).some
  let adjS := (proEtaleRingDerivedOperations_adjunction g S S' (Iso.refl _)).some
  let δ := proEtaleRingRestrictionDerivedDirectImage g R S R' S' φ φ'
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact ((pbcDerivedScalarAdjunction φ).comp adjS).leftAdjointUniq
    ((adjR.comp (pbcDerivedScalarAdjunction φ')).ofNatIsoRight δ.symm)

/-- The pulled-back consecutive tower transition is an isomorphism.

Source: Stacks Project, proetale.tex, Tag 09C6, consecutive quotient
normalization.  Apply the supplied normalization isomorphism of the adic
tower at `(n+1,n)`, transport it through inverse image, and paste the
canonical scalar restriction comparison.  The resulting map is exactly the
displayed pulled-back transition, so it is invertible.  This statement is the
tower-only part of the realization reduction.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-tower-transition).
-/
theorem adicTowerPullback_consecutive_transition_iso
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) (W : Y.Etale) (_w : W.left) :
    Nonempty
      ((pbcDerivedExtend ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
        ((adicTowerPullback (W.hom ≫ g)
          ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1))) ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  let f := W.hom ≫ g
  let q := pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)
  let e := pullbackScalarIso f q
  let h := (adicTowerPullback f ((pbcAdicRings X d).obj (op n))).mapIso
    (M.normalization (n + 1) n (Nat.le_succ n))
  exact ⟨e.symm.app (M.level (n + 1)) ≪≫ h⟩

end AlgebraicGeometry.Scheme
