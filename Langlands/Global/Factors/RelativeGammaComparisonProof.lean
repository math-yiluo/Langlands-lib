import Langlands.Global.Factors.RelativeGammaComparisonStatement
import Langlands.Global.Factors.HeckeTwistComparisonProof
import Langlands.Global.Factors.GermRationalComparisonProof

noncomputable section

set_option autoImplicit false

universe u uV uP uQ uE

namespace Langlands.Global.FunctionalEquationComparison

theorem relativeGammaComparison :
    RelativeGammaComparisonStatement.{u, uV, uP, uQ, uE} := by
  intro hisolate c _ F E _ _ _ _ _ _ _ ψ _ r t S S' T T' _ _ P P' v
    hI hA hI' hA' w e ι _ ψv _ eC ε hε hmeasure hdata
  refine ⟨hmeasure, ?_⟩
  intro ν hν
  obtain ⟨d, _, hanalytic, hinf, hfinite, hram, hout, _⟩ := hdata ν hν
  obtain ⟨χ₁, χ₂, B, _, _, _, _, hgamma⟩ :=
    heckeTwistComparison hisolate F d.badPlaces v d.selected_mem d.depth
      d.automorphicData d.arithmeticData hanalytic hinf hfinite hram hout
  have hequal : d.automorphicGamma = d.arithmeticGamma :=
    germRationalComparison _
      (Langlands.Global.CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality_gt_one
      _ _ _ _ d.automorphic_continuation d.arithmetic_continuation hgamma
  exact ⟨d.arithmeticGamma, hequal ▸ d.automorphic_spec, d.arithmetic_spec⟩

end Langlands.Global.FunctionalEquationComparison
