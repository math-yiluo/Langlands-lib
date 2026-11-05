import Langlands.Algebra.GenericIrreducibilityGenericFibre
import Langlands.Algebra.GenericIrreducibilityFractionTensor

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u v w t

open scoped TensorProduct

namespace Langlands.Algebra.GenericIrreducibilitySpreading

/-- Geometric irreducibility of the actual generic tensor spreads for a faithful
finite type domain algebra over a domain. -/
theorem exists_ne_zero_tensor_nilradical_isPrime
    {R : Type u} {C : Type v} {F : Type t}
    [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (hgen : (nilradical (AlgebraicClosure F ⊗[R] C)).IsPrime) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra R K],
      algebraMap R K a ≠ 0 → (nilradical (K ⊗[R] C)).IsPrime := by
  let : FaithfulSMul R (AlgebraicClosure F) :=
    FaithfulSMul.trans R F (AlgebraicClosure F)
  let : Algebra (FractionRing R) (FractionRing C) :=
    FractionRing.liftAlgebra R (FractionRing C)
  let : IsScalarTower R (FractionRing R) (FractionRing C) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing C)
  let : Algebra (FractionRing R) (AlgebraicClosure F) :=
    FractionRing.liftAlgebra R (AlgebraicClosure F)
  let : IsScalarTower R (FractionRing R) (AlgebraicClosure F) :=
    FractionRing.isScalarTower_liftAlgebra R (AlgebraicClosure F)
  apply exists_ne_zero_tensor_nilradical_isPrime_of_fractionFieldTensor
    (Ω := AlgebraicClosure F)
  exact GenericIrreducibilityReduction.nilradical_tensor_fractionField_isPrime
    (F := FractionRing R) (L := FractionRing C) hgen

end Langlands.Algebra.GenericIrreducibilitySpreading

namespace Langlands.Algebra

/-- The full affine algebraic generic geometric irreducibility spreading theorem. -/
theorem finiteTypeGeometricIrreducibilitySpreading :
    FiniteTypeGeometricIrreducibilitySpreading.{u,v,w} := by
  apply GenericIrreducibilityReduction.spreading_of_domain_bases
  intro S _ _ F _ _ _ C _ _ _ _ _ hgen
  exact GenericIrreducibilitySpreading.exists_ne_zero_tensor_nilradical_isPrime hgen

end Langlands.Algebra
