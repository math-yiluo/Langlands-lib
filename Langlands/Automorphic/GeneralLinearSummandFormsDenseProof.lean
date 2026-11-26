import Langlands.Automorphic.GeneralLinearSummandFormsNonzero
import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeProof

/-! # Density of the forms attached to an irreducible cuspidal summand of `GL_n` -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- **Density of attached form classes.** For a nonzero closed invariant subspace `P` of the
full almost-everywhere cuspidal `L²` space `S` of the positive rational quotient of `GL_{r+1}`,
with no closed invariant subspaces other than `0` and itself, every vector of `P` lies in the
closure in `S` of the classes of the stable cuspidal forms attached to `P`. This is the
single-summand density consequence of Getz–Hahn, Lemma 9.7.2 and (9.40) in the proof of
Theorem 9.7.3. -/
theorem generalLinearSummandFormsDense : GeneralLinearSummandFormsDenseStatement.{u} :=
  generalLinearSummandFormsDense_of_representative groupSchemeQuotientL2ContinuousRepresentative

end Langlands.Automorphic.GroupSchemeFunctions
