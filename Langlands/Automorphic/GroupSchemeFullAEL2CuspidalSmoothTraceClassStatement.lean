import Langlands.Analysis.OperatorIdeals
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Global.AdelicLocalFinitenessStatement

/-!
# Cuspidal trace class of smooth test functions from Hilbert–Schmidt test functions

`GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement`: if every adelic test function
(`IsAdelicTestFunction`) has a Hilbert–Schmidt cuspidal operator `R_cusp(f)`, then every adelic
test function has a trace-class cuspidal operator. It is the form of
`GroupSchemeFullAEL2CuspidalTraceClassStatement` with the analytic input asked only for test
functions and the conclusion reaching every test function. It is proved in
`GroupSchemeFullAEL2CuspidalSmoothTraceClassReduction`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- If every test function on `G(𝔸_F)` (in the sense of `IsAdelicTestFunction`) integrates the
original right action on the full almost-everywhere cuspidal space to a Hilbert–Schmidt operator,
then so does every test function to a trace-class operator. The parameters are those of
`GroupSchemeFullAEL2CuspidalTraceClassStatement`; the hypothesis is asked for test functions only,
and the conclusion reaches every test function, not only convolution products. -/
def GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    (∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG), IsAdelicTestFunction F G f →
      Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf)) →
    ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG), IsAdelicTestFunction F G f →
      Langlands.Analysis.OperatorIdeals.IsTraceClass
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf)

end Langlands.Automorphic.GroupSchemeFunctions
