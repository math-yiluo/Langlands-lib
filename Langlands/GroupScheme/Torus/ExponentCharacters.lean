import Langlands.GroupScheme.Torus.RelativeAdjointWeights
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Actual exponent characters over arbitrary bases -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

variable (S : Scheme.{u}) (I : Type u) [Fintype I]

/-- The actual character with a fixed integral exponent vector, over any base scheme. -/
def exponentCharacter (m : I → ℤ) : characterLattice (commGroupScheme S I) :=
  ∑ j, m j • proj S I j

/-- The actual character evaluates as its exponent monomial on every test scheme. -/
theorem pointsEquiv_exponentCharacter (m : I → ℤ)
    {U : Over S} (x : U ⟶ (splitTorus S I).X) :
    Gm.pointsEquiv S U (x ≫ (CommGroupScheme.groupHom (exponentCharacter S I m)).hom.hom) =
      ∏ j, pointsEquiv I U x j ^ m j := by
  unfold exponentCharacter
  refine (congrArg (Gm.pointsEquiv S U)
    (comp_groupHom_sum (G := commGroupScheme S I) x Finset.univ
      (fun j => m j • proj S I j))).trans ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  refine (congrArg (Gm.pointsEquiv S U)
    (comp_groupHom_zsmul (G := commGroupScheme S I) x (m j) (proj S I j))).trans ?_
  rw [map_zpow, comp_proj]

variable {S' : Scheme.{u}}

/-- Fixed-exponent actual characters commute with arbitrary base change,
through the canonical split-torus comparison. -/
theorem exponentCharacter_baseChange (b : S' ⟶ S) (m : I → ℤ) :
    (commBaseChangeIso b I).hom ≫ exponentCharacter S' I m =
      characterLattice.baseChange b _ (exponentCharacter S I m) := by
  simp only [exponentCharacter, Preadditive.comp_sum, Preadditive.comp_zsmul,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  rw [commBaseChangeIso_hom_proj]
  rfl

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- The fixed-exponent character value on an actual affine point is its
integral-exponent monomial, over arbitrary rings. -/
theorem characterValue_exponentCharacter (m : I → ℤ)
    (t : Lie.AffinePoints (splitTorus (Spec R) I) A) :
    Lie.characterValue (exponentCharacter (Spec R) I m) t =
      exponentValue I (algebraPointsEquiv I A t) (Multiplicative.ofAdd m) := by
  let q := Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv
  change q (Gm.pointsEquiv _ _ (t ≫
    (CommGroupScheme.groupHom (exponentCharacter (Spec R) I m)).hom.hom)) = _
  rw [pointsEquiv_exponentCharacter, map_prod]
  simp only [map_zpow]
  rfl

/-- Relative exponent weight spaces are the existing actual character
weight spaces for the canonical fixed-exponent characters, over any ring. -/
theorem exponentWeightSpace_eq_weightSpace_exponentCharacter
    (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec R) I ⟶ G) (m : I → ℤ) :
    exponentWeightSpace I G i m = weightSpace i (exponentCharacter (Spec R) I m) := by
  ext X
  constructor
  · intro h B _ _ t
    have h' := h B (algebraPointsEquiv I B t)
    rw [MulEquiv.symm_apply_apply, ← characterValue_exponentCharacter] at h'
    exact h'
  · intro h B _ _ t
    have h' := (mem_weightSpace.mp h) B ((algebraPointsEquiv I B).symm t)
    rw [characterValue_exponentCharacter, MulEquiv.apply_symm_apply] at h'
    exact h'

/-- Over a field, the canonical exponent character agrees with the existing
inverse of the integral character-lattice coordinate equivalence. -/
theorem exponentCharacter_eq_characterLatticeEquiv_symm
    (k : Type u) [Field k] (m : I → ℤ) :
    exponentCharacter (Spec (CommRingCat.of k)) I m =
      (characterLatticeEquiv k I).symm m :=
  (characterLatticeEquiv_symm_eq k I m).symm

end Langlands.GroupScheme.splitTorus
