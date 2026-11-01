import Langlands.Geometry.Analytic.StrictTestDomain.RationalRelativeComparison
import Langlands.Geometry.Analytic.StrictTestDomain.RationalSheafStatement
import Langlands.Geometry.Analytic.StrictTestDomain.WholeSpectrumRationalGluingProof

/-! # Finite rational gluing over a rational target -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

/-- Compatible sections on a finite rational cover uniquely glue in the actual
quotient algebra of the rational target. -/
theorem finiteRationalGluing : FiniteRationalGluingStatement.{u} := by
  intro K _ _ _ P d I _ D f hc s hs
  classical
  by_cases hI : IsEmpty I
  · let := hI
    exact existsUnique_gluing_empty d D f hc s
  · obtain ⟨a, ha, hu⟩ := wholeSpectrumRationalGluing K d.algebra I
      (fun i => (D i).pullback d.baseMap) hc.relative
      (fun i => (D i).comparison d.baseMap (s i))
      (compatible_comparison D d.baseMap s hs)
    have hmap (b : d.algebra) (i : I) :
        (D i).comparison d.baseMap ((f i).restriction b) =
          ((D i).pullback d.baseMap).baseMap b :=
      congrArg (fun g => g b) (f i).comparison_comp_restriction
    refine ⟨a, ?_, ?_⟩
    · intro i
      apply (f i).comparison_injective
      exact (hmap a i).trans (ha i)
    · intro b hb
      apply hu b
      intro i
      exact (hmap b i).symm.trans
        (congrArg ((D i).comparison d.baseMap) (hb i))

end Langlands.Analytic.StrictTestDomain
