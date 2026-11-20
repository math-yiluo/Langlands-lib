import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeKernelFactorizationReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonomorphismSpreadingProof

/-! # Canonical factorization of homomorphisms from groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- The kernel is of multiplicative type, and the homomorphism factors as its
affine fppf kernel quotient followed by a monomorphism (SGA 3, IX, Théorème 6.8). -/
theorem multiplicativeTypeKernelFactorization :
    MultiplicativeTypeKernelFactorizationStatement.{u} :=
  multiplicativeTypeKernelFactorization_of_rigidity_and_spreading
    multiplicativeTypeCentralRigidity multiplicativeTypeMonomorphismSpreading

end Langlands.GroupScheme
