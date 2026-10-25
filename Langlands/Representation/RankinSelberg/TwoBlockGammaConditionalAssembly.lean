import Langlands.Representation.RankinSelberg.TwoBlockGammaDescentObjects
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Mathlib.Algebra.Module.ULift

/-! Conditional assembly in a carrier universe closed under induction. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockGammaDescent

universe uF u

/-- A rank-one auxiliary object obtained from the trivial scalar character.
Only the supplied scalar full-type statement establishes its full type. -/
def twoBlockGammaAuxiliary
    (hScalar : RankOneWhittakerTypeStatement.{uF})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier) :
    Object.{uF, u} F ψ 0 := by
  letI := F.canonicalTopologicalData.topology
  let χ : Quasicharacter F.Carrier := 1
  let ρ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{max uF u} ℂ) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
  have e : (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)).Equiv ρ :=
    Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)
  exact ofRepresentation ρ ((hScalar p F ψ χ).of_equiv e)

/-- The seven explicit analytic/full-type inputs imply the exact two-block
gamma proposition in a stable common carrier universe. This is conditional
assembly, with no claim that any input has been proved. -/
theorem twoBlockGammaMultiplicativity_of_inputs_commonUniverse
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hSwap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (hDominant : TwoBlockGammaDominantRankStatement.{uF, max uF u, max uF u})
    (hAdjacent : TwoBlockGammaAdjacentRankStatement.{uF, max uF u, max uF u})
    (hRankOne : TwoBlockGammaRankOneStatement.{uF, max uF u, max uF u})
    (hScalar : RankOneWhittakerTypeStatement.{uF}) :
    TwoBlockGammaMultiplicativityStatement.{uF, max uF u, max uF u} := by
  intro p hp F ψ ν r t m h V hVAdd hVMod W hWAdd hWMod pi sigma hpi hsigma
  exact certified ν hInd hInput hSwap hDominant hAdjacent hRankOne
    (twoBlockGammaAuxiliary hScalar F ψ) r t m h pi sigma hpi hsigma

end Langlands.RankinSelberg
