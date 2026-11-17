import Langlands.GroupScheme.Reductive.AffineOpenIsogenyConjugacy
import Langlands.GroupScheme.Reductive.AffineSplitSurjectionRootDatumProof

/-! # Proof: isogenies agreeing on a maximal torus are locally torus conjugate -/

universe u

namespace Langlands.GroupScheme

/-- Isogenies of reductive group schemes agreeing on a maximal torus are
fppf-locally conjugate by that torus, with uniqueness modulo the centre. -/
theorem reductiveIsogenyTorusRigidity : ReductiveIsogenyTorusRigidityStatement.{u} :=
  reductiveIsogenyTorusRigidity_of_affineSplitSurjectionRootDatum
    affineSplitSurjectionRootDatum

end Langlands.GroupScheme
