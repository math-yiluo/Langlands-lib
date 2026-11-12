import Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentFiniteSets
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFProof

/-! # Proof of finite-surjective descent of finite-set affine neighborhoods

Gross, Theorem 1.2 (descent direction), specialized to an affine base: the published
reduction to a quasi-affine source, applied to the published quasi-affine-source case.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact, quasi-separated algebraic space over `Spec R` admitting a finite
surjection from an AF scheme is represented by an AF scheme over `Spec R`. -/
theorem finiteSurjectiveFiniteAffineNeighborhoodsDescent :
    FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement.{u} :=
  AFDescentFiniteSets.finiteAffineNeighborhoodsDescent_of_quasiAffineSourceAF
    finiteSurjectiveQuasiAffineSourceAF

end Langlands.AlgebraicGeometry.AlgebraicSpace
