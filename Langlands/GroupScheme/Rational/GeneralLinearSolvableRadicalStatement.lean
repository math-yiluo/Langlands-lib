import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # The solvable radical of the standard general linear group scheme -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The scalar torus is the geometric solvable radical of `GL_n` in positive
rank. The trivial torus is its geometric solvable radical in rank zero. -/
def GeneralLinearSolvableRadicalStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ n : ℕ, IsGeometricSolvableRadical
      (GeneralLinear.scalarTorus (Fin (n + 1)) (CommRingCat.of k))) ∧
    IsGeometricSolvableRadical
      (TorusExistence.trivialTorusHom (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of k)))

end Langlands.GroupScheme
