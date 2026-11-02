import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartRelativeComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSheafStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalGluingProof

/-! # Finite rational gluing over a positive-radius rational target -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

/-- Compatible scalar sections on a finite positive-radius rational cover
uniquely glue in the actual quotient algebra of the rational target. -/
theorem finiteRationalGluing : FiniteRationalGluingStatement.{u} := by
  intro K _ _ _ P d I _ D f hc s hs
  obtain ⟨a, ha, hu⟩ := wholeSpectrumRationalGluing K d.algebra I
    (fun i => pullback d.baseMap (D i)) hc.relative
    (fun i => pullbackMap d.baseMap (D i) (s i))
    (compatible_pullbackMap D d.baseMap s hs)
  have hmap (b : d.algebra) (i : I) :
      pullbackMap d.baseMap (D i) ((f i).restriction b) =
        (pullback d.baseMap (D i)).baseMap b :=
    congrArg (fun g => g b) (f i).pullbackMap_comp_restriction
  refine ⟨a, ?_, ?_⟩
  · intro i
    apply (f i).pullbackMap_injective
    exact (hmap a i).trans (ha i)
  · intro b hb
    apply hu b
    intro i
    exact (hmap b i).symm.trans
      (congrArg (pullbackMap d.baseMap (D i)) (hb i))

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
