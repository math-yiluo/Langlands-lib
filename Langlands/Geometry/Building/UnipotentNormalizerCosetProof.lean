import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.Geometry.Building.UnipotentNormalizerCosetReduction
import Langlands.Geometry.Building.ChamberIwahoriProof

/-! # Proof of the replaced normalizer-coset lemma (KP Lemma 5.3.5, 2024 corrections)

For every actual datum `P`, every chamber `C` and every generic cocharacter `ν`, and all
`n, n' ∈ N(F)`: `n = u n' p` for some `u ∈ U(F) = standardUnipotentPoints P.i ν ∅` and
`p ∈ P_C` if and only if `n' n⁻¹ ∈ Z(F)^0`.

The published per-data reduction `ParahoricBuildingData.unipotentNormalizerCoset_of_chamberIwahori`
derives this from the normality of `Z(F)^0` in `N(F)` and the chamber Iwahori decomposition.
Both are discharged by published proofs for every actual `P`:
`ParahoricBuildingData.normal_normalizerZero` and
`ParahoricBuildingData.chamberIwahoriDecomposition`.
-/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **KP Lemma 5.3.5, as replaced in the 2024 corrections.** For every chamber `C` of the
apartment, every generic cocharacter `ν` and all `n, n' ∈ N(F)`, `n ∈ U(F) n' P_C` if and only
if `n' n⁻¹ ∈ Z(F)^0`, where `U(F) = standardUnipotentPoints P.i ν ∅`. -/
theorem unipotentNormalizerCoset : UnipotentNormalizerCosetStatement.{u} := by
  intro F _ _ _ _ G _ P _ _ hP C ν hC hν
  have := P.normal_normalizerZero
  exact P.unipotentNormalizerCoset_of_chamberIwahori P.chamberIwahoriDecomposition hP C ν hC hν

end Langlands.Geometry.Building
