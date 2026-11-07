import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Correspondence.RankOneExistence
import Langlands.Correspondence.RankOneOperationCompatibility
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Smooth.Contragredient.Equivalence

/-! Smooth duality of the actual unramified principal series. -/

noncomputable section

namespace Langlands.Unramified

open Correspondence GeneralLinear Classification

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualityFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualityGLTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance dualityGLGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Inverting the uniformizer value inverts the actual unramified character. -/
theorem character_inv (z : ℂˣ) : character F z⁻¹ = (character F z)⁻¹ := by
  apply ContinuousMonoidHom.ext
  intro a
  change (z⁻¹) ^ (F.canonicalTopologicalData.ord a) =
    (z ^ (F.canonicalTopologicalData.ord a))⁻¹
  exact inv_zpow z _

/-- Evaluation identifies the smooth dual of an actual scalar GL1 character
with the scalar representation of the inverse character. -/
def scalarCharacterSmoothDualEquiv (χ : QuasiCharacter F) :
    (smoothContragredient (characterRepresentation (determinantQuasiCharacter F 1 χ))).Equiv
      (characterRepresentation (determinantQuasiCharacter F 1 χ⁻¹)) := by
  let e := scalarCharacterDualEquiv (determinantQuasiCharacter F 1 χ)
  let eInv := FiniteRepresentation.characterLineEquiv.{uF, 0}
    (determinantQuasiCharacter F 1 χ⁻¹)
  have hInv : IsSmooth (characterRepresentation (determinantQuasiCharacter F 1 χ⁻¹)) :=
    isSmooth_of_surjective eInv.toIntertwiningMap eInv.surjective
      (rankOneCharacterObject.{uF, 0} F χ⁻¹).isSmooth
  have hDual : IsSmooth (characterRepresentation (determinantQuasiCharacter F 1 χ)).dual :=
    isSmooth_of_surjective e.symm.toIntertwiningMap e.symm.surjective hInv
  exact (smoothEquiv hDual).trans e

set_option maxHeartbeats 800000 in
/-- The smooth contragredient of the actual normalized upper-Borel unramified
principal series is the actual principal series of the inverse tuple. -/
def principalSeriesOfTupleSmoothDualEquiv {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    (smoothContragredient (principalSeriesOfTuple F z)).Equiv
      (principalSeriesOfTuple F (fun i => (z i)⁻¹)) := by
  let T := F.canonicalTopologicalData
  let B := borelShape r
  let τ := fun i : Fin B.length => characterRepresentation (determinantQuasiCharacter F 1 (character F (z i)))
  have hτ : ∀ i, IsAdmissible (τ i) := by
    intro i
    exact isAdmissible_of_equiv (FiniteRepresentation.characterLineEquiv.{uF, 0}
      (determinantQuasiCharacter F 1 (character F (z i))))
      (rankOneSupercuspidalObject.{uF, 0} F (character F (z i))).property.2.1
  let e0 := (CuspidalProductContragredient.nonempty_contragredient_productEquiv T B τ hτ).some
  apply e0.trans
  apply T.normalizedProductInducedEquiv B
  intro i
  exact (scalarCharacterSmoothDualEquiv F (character F (z i))).trans
    (equivOfRepresentationEq (congrArg
      (fun χ : QuasiCharacter F => characterRepresentation (determinantQuasiCharacter F 1 χ))
      (character_inv F (z i))).symm)

end Langlands.Unramified
