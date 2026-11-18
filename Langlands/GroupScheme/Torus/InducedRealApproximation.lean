import Langlands.AlgebraicGeometry.PointTopology.RealApproximationOpen
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof
import Langlands.GroupScheme.Torus.WeilRestrictionRational

/-! # Real approximation for induced tori and Weil restrictions of `𝔾ₘ` -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace WeilGmRational

local instance (B : Type) [CommRing B] [Algebra ℚ B] [Module.Finite ℚ B] :
    IsAffine (WeilGm.groupScheme (CommRingCat.of ℚ) B).X.left :=
  IsAffine.of_isIso (leftIso (Module.finBasis ℚ B)).hom

/-- Real approximation for the Weil restriction of `𝔾ₘ` from any finite rational algebra. -/
theorem hasRealApproximation (B : Type) [CommRing B] [Algebra ℚ B] [Module.Finite ℚ B] :
    HasRealApproximation (WeilGm.groupScheme (CommRingCat.of ℚ) B).X := by
  let n := Module.finrank ℚ B
  let b : Module.Basis (Fin n) ℚ B := Module.finBasis ℚ B
  let X : Over (Spec (CommRingCat.of ℚ)) :=
    Over.mk (𝔸(ULift (Fin n); Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))
  let : IsAffine X.left :=
    IsAffine.of_isIso (AffineSpace.SpecIso (ULift (Fin n)) (CommRingCat.of ℚ)).hom
  let f : (WeilGm.groupScheme (CommRingCat.of ℚ) B).X ⟶ X :=
    Over.homMk (weilChart b) (weilChart_over b)
  let : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (weilChart b))
  exact (hasRealApproximation_affineSpace (ULift (Fin n))).of_isOpenImmersion f

end WeilGmRational

/-- Rational points of an induced rational torus are dense in its real points. -/
def InducedTorusRealApproximationStatement : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine T.X.left],
    IsInducedTorus T → HasRealApproximation T.X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem inducedTorusRealApproximation : InducedTorusRealApproximationStatement := by
  intro T _ hT
  obtain ⟨L, hL, hA, hF, hG, hs, hb⟩ := hT
  let := hL
  let := hA
  let := hF
  let := hG
  obtain ⟨n, E, ⟨e⟩⟩ :=
    inducedTorusWeilDecomposition ℚ L T hs ⟨L, hL, hA, hF, hG, hs, hb⟩
  -- Use the field inclusions from the decomposition to define the product algebra.
  let : Algebra ℚ (∀ i, E i) :=
    @Pi.algebra _ _ (fun i => E i) _ _ (fun i => (E i).algebra)
  let eGroup : T.toGrp ≅ _ :=
    { hom := e.hom.toMul
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg Additive.toMul e.hom_inv_id
      inv_hom_id := congrArg Additive.toMul e.inv_hom_id }
  have hfinite : Module.Finite ℚ (∀ i, E i) := inferInstance
  have h := @WeilGmRational.hasRealApproximation (∀ i, E i) _ _ hfinite
  let : IsAffine _ := IsAffine.of_isIso
    (WeilGmRational.leftIso (k := ℚ) (B := ∀ i, E i) (Module.finBasis ℚ (∀ i, E i))).hom
  exact h.of_iso ((Grp.forget _).mapIso eGroup).symm

end Langlands.GroupScheme
