import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedAllGrowth
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceModelTCStatement

/-! # The totally complex pole theorem from its functional-equation and complex inputs -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField
open scoped Classical

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal InfiniteWhittakerSlice

/-- Over a totally complex number field the specified slice comparison follows from the
archimedean slice model at that field and the complex restriction surjectivity alone: there
are no real places. -/
theorem specifiedWhittakerSliceComparisonAt_of_complex
    (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)]
    (hSlice : InfiniteWhittakerSliceModelAt.{u,uQ} F)
    (hComplex : ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u}) :
    SpecifiedWhittakerSliceComparisonAt.{u,uQ} F := by
  have hRP : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1) v.2⟩
  intro ψ hψ r T hT P hP aR haR aC haC dR hdR dC hdC
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  let ψ' := inverseCharacter ψ
  have hψ' (x : F) : ψ' (algebraMap F (Adeles F) x) = 1 := by
    change inverseCharacter ψ _ = 1
    rw [inverseCharacter_apply, hψ, inv_one]
  have hχ' := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ' hψ'
  let M := Classical.choice (hSlice r T P hP ψ.complex hχ dR hdR dC hdC)
  let N := Classical.choice (hSlice r T P hP ψ'.complex hχ' dR hdR dC hdC)
  have hM := hasActualPlaceWhittakerRanges_of_cuspidal hT ψ hψ M
  have hN := hasActualPlaceWhittakerRanges_of_cuspidal hT ψ' hψ' N
  refine ⟨M, N, ⟨fun v => isEmptyElim v, fun w => le_antisymm ?_ ?_⟩,
    ⟨fun v => isEmptyElim v, fun w => le_antisymm ?_ ?_⟩⟩
  · intro W hW
    exact (archimedeanPlaceWhittakerModels.2 F ψ hψ r T w (aC w) (haC w) (dC w) (hdC w) W).1
      ((hM.2 w W).mp hW)
  · intro W hW
    exact (hM.2 w W).mpr ((hComplex F ψ hψ r T hT w (aC w) (haC w) (dC w) (hdC w) W).1 hW)
  · intro W hW
    apply (archimedeanPlaceWhittakerModels.2 F ψ hψ r T w (aC w) (haC w) (dC w) (hdC w) W).2
    simpa only [ψ', complex_inverseCharacter] using (hN.2 w W).mp hW
  · intro W hW
    apply (hN.2 w W).mpr
    simpa only [ψ', complex_inverseCharacter] using
      (hComplex F ψ hψ r T hT w (aC w) (haC w) (dC w) (hdC w) W).2 hW

/-- The totally complex completed equation, complex ordinary generation, the archimedean slice
model over totally complex fields and the complex restriction surjectivity imply the totally
complex cuspidal pair pole proposition in both universes. -/
def CuspidalPairPoleTCRemainingInputsStatement : Prop :=
  CuspidalPairCompletedEquationTCStatement.{u,uQ} →
  ComplexOrdinaryNormalizedGenerationStatement →
  InfiniteWhittakerSliceModelTCStatement.{u,uQ} →
  ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  CuspidalPairPoleTCStatement.{u,uQ}

theorem cuspidalPairPoleTCRemainingInputs : CuspidalPairPoleTCRemainingInputsStatement.{u,uQ} := by
  intro hFE hCG hSlice hComplex
  exact cuspidalPairPoleTCFromLocalTests hFE complexOrdinaryNormalizedAllGrowth.1 hCG
    complexOrdinaryNormalizedAllGrowth.2
    (fun F _ _ _ _ => specifiedWhittakerSliceComparisonAt_of_complex F (hSlice F) hComplex)

end Langlands.Global.CuspidalPairPoles
