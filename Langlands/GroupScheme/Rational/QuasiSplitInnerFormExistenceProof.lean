import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Adjoint.ExistenceProof

/-! # Existence of quasi-split inner forms of connected reductive field groups -/

universe u

namespace Langlands.GroupScheme

/-- **Existence of quasi-split inner forms** (Conrad, *Reductive group schemes* (2014),
Proposition 7.2.11 and Section 7.2). Every connected reductive group over an arbitrary
field is an actual finite-Galois inner twist of a quasi-split group, with an
adjoint-valued discrepancy cocycle. -/
theorem quasiSplitInnerFormExistence : QuasiSplitInnerFormExistenceStatement.{u} :=
  quasiSplitInnerFormExistence_of_rootDatum_adjoint rootDatumExistence
    adjointQuotientExistence

end Langlands.GroupScheme
