import Langlands.AlgebraicGeometry.Picard.SmoothFamilyFinitePresentationStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalComparisonProof

/-!
# Local finite presentation of a universal smooth-family parameter: proof

Over a quasi-separated base, the parameter of every universal rigidified smooth-family
algebraically trivial family on quasi-separated tests is isomorphic over the base to an
abelian scheme. Abelian schemes are smooth, hence locally of finite presentation, and this
property transports along the isomorphism.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the actual parameter scheme of every universal rigidified
smooth-family algebraically trivial family on quasi-separated tests is locally of finite
presentation over the base. -/
theorem smoothFamilyFinitePresentation :
    SmoothFamilyFinitePresentationStatement.{u} := by
  intro S _ A P L hL
  obtain ⟨B, M, hM⟩ :=
    smoothFamilyAbelianRepresentabilityOfFiniteType.{u}
      finiteTypeSmoothFamilyAbelianRepresentability.{u} S A
  let : QuasiSeparatedSpace B.X.left :=
    quasiSeparatedSpace_of_quasiSeparated B.X.hom
  obtain ⟨e, _, _⟩ :=
    smoothFamilyUniversalComparison S A B.X P M L hM hL
  have : IsIso e.inv.left := by
    change IsIso ((Over.forget S).map e.inv)
    infer_instance
  have htriangle : e.inv.left ≫ B.X.hom = P.hom := Over.w e.inv
  rw [← htriangle]
  infer_instance

end Langlands.AbelianScheme
