import Langlands.Representation.Smooth.Factorization.RestrictedTensorAdmissibilityProof
import Langlands.Representation.Smooth.Factorization.RestrictedTensorIrreducibilityProof
import Langlands.Representation.Smooth.Factorization.RestrictedTensorReferenceIndependenceProof
import Langlands.Representation.Smooth.Factorization.RestrictedTensorUniquenessProof

/-!
# Flath's Example 2

Proof of `FlathRestrictedTensorStatement` (Flath 1979, §2, Example 2, with the uniqueness of
the local factors): the conjunction of the four proved clauses.
-/

namespace Langlands

universe uI uG uV uW

/-- **Flath's Example 2** (Flath 1979, §2): admissibility, irreducibility, reference
independence and uniqueness of the local factors for restricted tensor representations. -/
theorem flathRestrictedTensor : FlathRestrictedTensorStatement.{uI, uG, uV, uW} :=
  ⟨restrictedTensorAdmissibility, restrictedTensorIrreducibility,
    restrictedTensorReferenceIndependence, restrictedTensorFactorUniqueness⟩

end Langlands
