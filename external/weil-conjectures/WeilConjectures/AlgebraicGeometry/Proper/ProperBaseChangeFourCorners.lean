/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
/-!
# Four finite-level proper base-change corners
The finite constant coefficient presentation and its inverse limit are the recorded
completed-coefficient datum. Its normalized comparison identifies finite coefficients
with sheafified continuous component functions and respects quotient transitions.
The reduction/pullback comparison is characterized on K-flat representatives by
the mate of sectionwise restriction/direct-image commutation, fixing its tensor map.

## References

* Stacks Tags 099N, 09C9, 0B56 and 0944
* Stacks 098T
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory
variable {A : Type (t + 1)} [CommRing A]

/-- The actual quotient ring tower, with exponent n+1 and its consecutive quotient maps. -/
def fourCornerRingTower (I : Ideal A) : ℕᵒᵖ ⥤ CommRingCat.{t + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ CommRingCat.of (A ⧸ I ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))

/-- Every quotient in the adic datum is finite, including the first positive level. -/
instance fourCornerRingTowerFinite (d : ProEtaleAdicCoefficientDatum A) (n : ℕᵒᵖ) :
    Finite ((fourCornerRingTower d.ideal).obj n) := d.quotientFinite n.unop

/-- Constant sheafification commutes with the presentation of the strict quotient sequence. -/
theorem fourCornerCoefficientTowerNaturality (T : Scheme.{t})
    (d : ProEtaleAdicCoefficientDatum A) {i j : ℕᵒᵖ} (h : i ⟶ j) :
    (proEtaleCoefficientTower T (fourCornerRingTower d.ideal)).map h =
      (adicLisseRingSystem T d.ideal).map h := by
  let e : proEtaleCoefficientTower T (fourCornerRingTower d.ideal) ⟶
      adicLisseRingSystem T d.ideal :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [proEtaleCoefficientTower, Functor.comp_map, fourCornerRingTower,
        adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id,
        Category.id_comp])
  simpa only [e, NatTrans.ofOpSequence_app, Category.comp_id, Category.id_comp] using
    (show _ from e.naturality h)

/-- The identity-on-objects isomorphism of the two strict coefficient presentations. -/
def fourCornerCoefficientTowerIso (T : Scheme.{t}) (d : ProEtaleAdicCoefficientDatum A) :
    proEtaleCoefficientTower T (fourCornerRingTower d.ideal) ≅
      adicLisseRingSystem T d.ideal :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun h ↦ (Category.comp_id _).trans
      ((fourCornerCoefficientTowerNaturality T d h).trans (Category.id_comp _).symm))

/-- The specified profinite inverse-image comparison at the actual completed ring. -/
def fourCornerCoefficientIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj (adicDatumRing V d) ≅
      adicDatumRing U d :=
  (proEtaleSheafInverseImage f CommRingCat.{t + 1}).mapIso
      (lim.mapIso (fourCornerCoefficientTowerIso V d)).symm ≪≫
    @asIso _ _ _ _ (proEtaleProfiniteComparison f (fourCornerRingTower d.ideal))
      ((proEtale_profinite_coefficient_inverse_image (fourCornerRingTower d.ideal)).2.1 U V f) ≪≫
    lim.mapIso (fourCornerCoefficientTowerIso U d)

/-- The specified finite coefficient comparison, normalized by constant sections. -/
def fourCornerFiniteIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj
        ((adicLisseRingSystem V d.ideal).obj (op n)) ≅
      (adicLisseRingSystem U d.ideal).obj (op n) :=
  @asIso _ _ _ _ ((proEtaleConstantComparison f).app
    ((fourCornerRingTower d.ideal).obj (op n)))
      ((proEtale_profinite_coefficient_inverse_image (fourCornerRingTower d.ideal)).1 U V f (op n))

/-- The completed and finite comparisons commute with their actual limit projections. -/
theorem fourCornerProjectionComm {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    (fourCornerCoefficientIso f d).hom ≫ adicDatumProjection U d n =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
        (adicDatumProjection V d n) ≫ (fourCornerFiniteIso f d n).hom := by
  let F := proEtaleSheafInverseImage f CommRingCat.{t + 1}
  let eV := fourCornerCoefficientTowerIso V d
  let eU := fourCornerCoefficientTowerIso U d
  let p := proEtaleProfiniteComparison f (fourCornerRingTower d.ideal)
  have hp := (proEtale_profinite_coefficient_inverse_image
    (fourCornerRingTower d.ideal)).2.2.1 U V f (op n)
  have hh : eU.hom.app (op n) = 𝟙 _ := rfl
  have hi : eV.inv.app (op n) = 𝟙 _ := rfl
  change F.map (limMap eV.inv) ≫ p ≫ limMap eU.hom ≫
    limit.π (adicLisseRingSystem U d.ideal) (op n) = _
  calc
    _ = F.map (limMap eV.inv) ≫
        (p ≫ limit.π (proEtaleCoefficientTower U (fourCornerRingTower d.ideal)) (op n)) := by
      rw [limMap_π, hh, Category.comp_id]
    _ = F.map (limMap eV.inv) ≫
        (F.map (limit.π (proEtaleCoefficientTower V (fourCornerRingTower d.ideal)) (op n)) ≫
          (fourCornerFiniteIso f d n).hom) :=
      congrArg (fun k ↦ F.map (limMap eV.inv) ≫ k) hp
    _ = _ := by
      rw [← F.map_comp_assoc, limMap_π, hi, Category.comp_id]
      rfl

end AlgebraicGeometry.Scheme
