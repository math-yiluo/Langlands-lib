import Langlands.Automorphic.Unramified.StrongBaseChangeSupportReductionStatement
import Langlands.Automorphic.Unramified.WeakInductionOrbitRestriction
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceComparisons

/-!
# B7 and its totally complex form from strong cyclic base change

`cyclicWeakBaseChangeComplexPlaceReduction` proves
`CyclicWeakBaseChangeComplexPlaceReductionStatement` and
`cyclicWeakBaseChangeComplexPlaceReductionTC` proves
`CyclicWeakBaseChangeComplexPlaceReductionTCStatement`. Only the complex-place clause C of the
premise `CyclicStrongBaseChangeSupportStatement` is used. See the paired Markdown.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open Langlands.Automorphic.CuspidalOperatorRealization
open ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- **B7 from strong cyclic base change.** Clause C of the premise, applied to the singletons
of the two cuspidal classes, to the singleton of the induced class and the Galois orbit of the
inducing class, and to the given isobaric data, gives the three clauses of
`CyclicWeakBaseChangeComplexPlaceStatement`. -/
theorem cyclicWeakBaseChangeComplexPlaceReduction :
    CyclicWeakBaseChangeComplexPlaceReductionStatement.{uF, uE, uV, uW} := by
  intro hBC F E _ _ _ _ _ _ _ _ _ hprime
  have hC := hBC.2.2.1 F E hprime
  refine ⟨?_, ?_, fun DF DE hDF hDE hW v w ds => hC DF DE hDF hDE hW v w ds⟩
  · intro r S T hS hW v w ds
    have hT : HasUnitaryCentralCharacter T :=
      hasUnitaryCentralCharacter_of_isWeakBaseChangeOf.{uF, uE, uV, uW} S T hS hW
    have h := hC (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass))
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
      (IsobaricData.isUnitary_ofCuspidal.mpr (S.isUnitarizable_of_hasUnitaryCentralCharacter hS))
      (IsobaricData.isUnitary_ofCuspidal.mpr (T.isUnitarizable_of_hasUnitaryCentralCharacter hT))
      ((IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff T.isoClass S.isoClass).mpr hW) v w ds
    simp only [IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff] at h
    exact h
  · intro r m S T hT _ hInd v d e ds hds
    have hS : HasUnitaryCentralCharacter S :=
      weakInductionUnitaryCentralCharacter.{uF, uE, uV, uW} F E r m S T hT hInd
    obtain ⟨w⟩ := nonempty_infinitePlacesAbove (E := E) v.1
    have h := hC (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass))
      (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
      (IsobaricData.isUnitary_ofCuspidal.mpr (S.isUnitarizable_of_hasUnitaryCentralCharacter hS))
      (isUnitary_galoisOrbit_of_hasUnitaryCentralCharacter T hT)
      (weakInductionOrbitBaseChange.{uF, uE, uV, uW} F E S.isoClass T.isoClass hInd)
      v w (complexPlaceLanglandsSum v e ds)
    have h' := h.mpr (galoisOrbit_hasComplexPlaceParameter T v w e ds hds)
    rw [IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff] at h'
    exact h'

/-- **Totally complex B7 from strong cyclic base change.** The totally complex conclusion is
the general one at a totally complex base field. -/
theorem cyclicWeakBaseChangeComplexPlaceReductionTC :
    CyclicWeakBaseChangeComplexPlaceReductionTCStatement.{uF, uE, uV, uW} := by
  intro hBC F E _ _ _ _ _ _ _ _ _ _ hprime
  exact cyclicWeakBaseChangeComplexPlaceReduction.{uF, uE, uV, uW} hBC F E hprime

end Langlands.Automorphic.Unramified
