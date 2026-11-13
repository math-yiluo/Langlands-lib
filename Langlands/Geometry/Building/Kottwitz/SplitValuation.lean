import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Geometry.Building.IntegerValuation

/-! # Intrinsic valuation of a split torus over a discretely valued field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

variable {k : Type u} [Field k]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (hT : IsSplitTorus T.toGrp)

/-- The perfect pairing identifies actual cocharacters with the integral character dual. -/
def cocharacterDualEquiv :
    cocharacterLattice T ≃ₗ[ℤ] Module.Dual ℤ (characterLattice T) := by
  letI := CocharacterUniformizer.latticePairing_isPerfPair k T hT
  exact LinearEquiv.ofBijective (latticePairing T).flip
    (LinearMap.IsPerfPair.bijective_right (latticePairing T))

@[simp] theorem cocharacterDualEquiv_apply
    (ν : cocharacterLattice T) (χ : characterLattice T) :
    cocharacterDualEquiv T hT ν χ = latticePairing T χ ν := rfl

/-- Actual character evaluations followed by the source-positive integer order. -/
def characterOrderDual (v : Valuation k (WithZero (Multiplicative ℤ))) :
    rationalPoints T.toGrp →* Multiplicative (Module.Dual ℤ (characterLattice T)) where
  toFun t := Multiplicative.ofAdd
    (((IntegerValuation.rationalCharacterValuation v T.toGrp t).toAdd.comp
      (rationalCharacters.equivCharacterLattice T).symm.toAddMonoidHom).toIntLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro χ
    change (IntegerValuation.rationalCharacterValuation v T.toGrp 1).toAdd
      ((rationalCharacters.equivCharacterLattice T).symm χ) = 0
    simp
  map_mul' t s := by
    apply LinearMap.ext
    intro χ
    change (IntegerValuation.rationalCharacterValuation v T.toGrp (t * s)).toAdd
        ((rationalCharacters.equivCharacterLattice T).symm χ) =
      (IntegerValuation.rationalCharacterValuation v T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice T).symm χ) +
      (IntegerValuation.rationalCharacterValuation v T.toGrp s).toAdd
        ((rationalCharacters.equivCharacterLattice T).symm χ)
    rw [map_mul]
    rfl

/-- The split-torus valuation is the inverse perfect pairing applied to character orders.
No local-field structure on `k` is required. -/
def splitValuation (v : Valuation k (WithZero (Multiplicative ℤ))) :
    rationalPoints T.toGrp →* Multiplicative (cocharacterLattice T) :=
  (cocharacterDualEquiv T hT).symm.toAddEquiv.toAddMonoidHom.toMultiplicative.comp
    (characterOrderDual T v)

/-- The construction has the source's defining character-pairing law. -/
theorem splitValuation_pairing (v : Valuation k (WithZero (Multiplicative ℤ)))
    (t : rationalPoints T.toGrp) (χ : characterLattice T) :
    latticePairing T χ (splitValuation T hT v t).toAdd =
      (IntegerValuation.orderUnits v
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ) t)).toAdd := by
  have h := LinearMap.congr_fun
    ((cocharacterDualEquiv T hT).apply_symm_apply (characterOrderDual T v t).toAdd) χ
  exact h

/-- Any homomorphism with the same pairing law is the constructed valuation. -/
theorem splitValuation_unique (v : Valuation k (WithZero (Multiplicative ℤ)))
    (w : rationalPoints T.toGrp →* Multiplicative (cocharacterLattice T))
    (hw : ∀ t χ, latticePairing T χ (w t).toAdd =
      (IntegerValuation.orderUnits v
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ) t)).toAdd) :
    w = splitValuation T hT v := by
  apply MonoidHom.ext
  intro t
  apply Multiplicative.toAdd.injective
  apply (cocharacterDualEquiv T hT).injective
  apply LinearMap.ext
  intro χ
  rw [cocharacterDualEquiv_apply, cocharacterDualEquiv_apply,
    hw, splitValuation_pairing]

end Langlands.Geometry.Building.Kottwitz
