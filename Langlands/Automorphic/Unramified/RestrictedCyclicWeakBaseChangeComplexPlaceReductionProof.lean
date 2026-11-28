import Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement
import Langlands.Automorphic.Unramified.WeakInductionOrbitRestriction
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceComparisons

/-!
# Restricted B7 from the restricted complex-place compatibility

`restrictedCyclicWeakBaseChangeComplexPlaceReduction` proves
`RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement`. See the paired Markdown.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open Langlands.Automorphic.CuspidalOperatorRealization

/-- **Restricted B7 from the restricted complex-place compatibility.** The premise, applied to
the singleton of the upper cuspidal class for (1)r and to the Galois orbit of the inducing class
for (2)r, gives the two clauses of `RestrictedCyclicWeakBaseChangeComplexPlaceStatement`. -/
theorem restrictedCyclicWeakBaseChangeComplexPlaceReduction :
    RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement.{uF, uE, uV, uW} := by
  intro hR F E _ _ _ _ _ _ _ _ _ _ hprime v₀ hv₀ w₀ wc hw₀ hwc
  refine ⟨?_, ?_⟩
  · intro r S T hS hT hS₀ hSc _ _ hW v w ds
    have h := hR F E hprime v₀ hv₀ w₀ wc hw₀ hwc r S
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass)) hS hS₀ hSc
      (IsobaricData.isUnitary_ofCuspidal.mpr (T.isUnitarizable_of_hasUnitaryCentralCharacter hT))
      ((IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff T.isoClass S.isoClass).mpr hW) v w ds
    simp only [IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff] at h
    exact h
  · intro r m S T hS hT hS₀ hSc _ _ _ hInd v d e ds hds
    obtain ⟨w⟩ := nonempty_infinitePlacesAbove (E := E) v.1
    have h := hR F E hprime v₀ hv₀ w₀ wc hw₀ hwc r S
      (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass)) hS hS₀ hSc
      (isUnitary_galoisOrbit_of_hasUnitaryCentralCharacter T hT)
      (weakInductionOrbitBaseChange.{uF, uE, uV, uW} F E S.isoClass T.isoClass hInd)
      v w (complexPlaceLanglandsSum v e ds)
    have h' := h.mpr (galoisOrbit_hasComplexPlaceParameter T v w e ds hds)
    rw [IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff] at h'
    exact h'

end Langlands.Automorphic.Unramified
