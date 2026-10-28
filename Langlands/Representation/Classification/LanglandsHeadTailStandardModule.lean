import Langlands.Representation.Classification.LanglandsTailDatum
import Langlands.Representation.Parabolic.HeadTailProductInduction

/-! Split a genuine Langlands standard module into its first twisted block and tail. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.TemperedLanglandsDatum

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n k : ℕ}
  (d : TemperedLanglandsDatum.{uV, uF} T n) (h : d.shape.length = k + 2)

/-- The original first twisted block and the standard module of the genuine tail datum. -/
abbrev headTailStandardFactors :
    letI := T.topology
    ∀ i : Fin 2, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear ((d.shape.headTailShape h).size i) F.Carrier) :=
  letI := T.topology
  fun i => match i with
    | 0 => SmoothRep.universeLift.{uF}
      (T.twistedBlocks d.shape d.blocks d.exponent (d.shape.headIndex h))
    | 1 => (d.tail h).standardModule

@[simp]
theorem headTailStandardFactors_zero :
    letI := T.topology
    d.headTailStandardFactors h (0 : Fin 2) =
      SmoothRep.universeLift.{uF}
        (T.twistedBlocks d.shape d.blocks d.exponent (d.shape.headIndex h)) := rfl

@[simp]
theorem headTailStandardFactors_one :
    letI := T.topology
    d.headTailStandardFactors h (1 : Fin 2) = (d.tail h).standardModule := rfl

/-- Specializing product regrouping uses the genuine Langlands tail without a new lift. -/
theorem headTailStandardFactors_eq :
    letI := T.topology
    T.headTailProductFactors d.shape h (T.twistedBlocks d.shape d.blocks d.exponent) =
      d.headTailStandardFactors h := by
  let := T.topology
  funext i
  fin_cases i <;> rfl

/-- Regroup the actual standard module using the original first block and genuine tail. -/
def headTailStandardModuleIso :
    letI := T.topology
    d.standardModule ≅
      (T.normalizedProductInductionFunctor (d.shape.headTailShape h)).obj
        (d.headTailStandardFactors h) := by
  letI := T.topology
  exact T.headTailProductInductionIso d.shape h
      (T.twistedBlocks d.shape d.blocks d.exponent) ≪≫
    (T.normalizedProductInductionFunctor (d.shape.headTailShape h)).mapIso
      (eqToIso (d.headTailStandardFactors_eq h))

/-- The corresponding actual equivalence preserves the ambient group and normalized action. -/
def headTailStandardModuleEquiv :
    letI := T.topology
    Representation.Equiv d.standardModule.representation
      (T.normalizedProductInduced (d.shape.headTailShape h)
        (fun i => (d.headTailStandardFactors h i).representation)) :=
  letI := T.topology
  SmoothRep.equivOfIso (d.headTailStandardModuleIso h)

end Langlands.PadicField.TopologicalData.TemperedLanglandsDatum
