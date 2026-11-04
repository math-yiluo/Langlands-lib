import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeStatement
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProduct
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeSeries

/-! # The split solvable envelope inside pseudo-parabolic subgroups -/

universe u

namespace Langlands.GroupScheme

/-- **CGP C.2.5, split solvable envelope.** For a pseudo-parabolic subgroup `P` of a smooth
connected affine group over a field, a maximal split torus `S` of `P` and a split unipotent
radical `U` of `P`, the semidirect product `U ⋊ S` is split solvable and maps onto the
fppf-local product of `S` and `U` inside `P`. -/
theorem pseudoParabolicSplitSolvableEnvelope :
    PseudoParabolicSplitSolvableEnvelopeStatement.{u} := by
  intro k _ G P _ _ _ i hi S s hs U j hj
  exact SplitSolvableEnvelope.exists_envelope_of_isSplitSolvable s j hi.isClosedSubgroup hs.1 hj
    (fun a => a.isSplitSolvableGroupScheme_semidirectProduct hs.1.1 hj.isSplitUnipotent)

end Langlands.GroupScheme
