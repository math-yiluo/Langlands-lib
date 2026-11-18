import Langlands.Global.Arithmetic.ChebotarevStatement
import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof
import Langlands.Global.Arithmetic.FiniteGaloisFrobeniusRigidityProof

/-!
# Finite Galois Chebotarev realization and character rigidity

The conjunction `ChebotarevRigidityStatement` is the pair of the Library's two published
conjunct proofs: `chebotarevPrimeRealizationStatement` (Chebotarev's theorem, existence form)
and `finiteGaloisFrobeniusRigidityStatement` (Frobenius-trace rigidity of finite Galois
representations).
-/

universe u v w z

namespace Langlands.Global

/-- **Finite Galois Chebotarev realization and character rigidity.** Every automorphism of a
finite Galois extension of number fields is an arithmetic Frobenius above an unramified prime
outside any finite set, and finite-dimensional complex representations of the Galois group are
determined by their unramified Frobenius traces outside a finite set. -/
theorem chebotarevRigidityStatement : ChebotarevRigidityStatement.{u, v, w, z} :=
  ⟨chebotarevPrimeRealizationStatement, finiteGaloisFrobeniusRigidityStatement⟩

end Langlands.Global
