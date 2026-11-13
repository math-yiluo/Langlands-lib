import Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction
import Langlands.Representation.Intertwining.PQBoundaryVanishingCompactSupportProof
import Langlands.Representation.Intertwining.PQCompositionProductDecomposition
import Langlands.Representation.Intertwining.PQCompositionHaarProof
import Langlands.Representation.Intertwining.PQCompositionLeviIntersection

/-! # Renard VII.3.5 (i): composition of integral-normalized intertwining operators -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VII.3.5 (i): under `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`, compatible
Haar measures exist, `P₁P₃`-regularity implies `P₂P₃`- and `P₁P₂`-regularity, and
`J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ) = J_{P₃|P₁}(σ)` for compatible measures. It is the published
reduction `pqIntertwiningComposition_of_reductions` applied to the proofs of its four
premises. -/
theorem pqIntertwiningComposition : PQIntertwiningCompositionStatement.{u, v} :=
  pqIntertwiningComposition_of_reductions pqBoundaryVanishingCompactSupport pqCompositionProduct
    pqCompositionHaar pqCompositionRegularity

end Langlands.Aubert.General.RepresentedParabolic
