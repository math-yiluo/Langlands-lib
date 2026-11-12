import Langlands.Representation.CuspidalSupport.RationalCompactRestrictionInertiaReduction
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof

/-! # The actual rational compact-restriction inertia decomposition -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- An irreducible smooth representation of the actual rational-point group whose
restriction to the actual common norm kernel has compact smooth-dual coefficients
admits the inertia category decomposition, from the published proofs of Renard
VI.3.2(ii) and VI.3.2(iii). -/
theorem rationalCompactRestrictionInertiaDecomposition :
    RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV} :=
  rationalCompactRestrictionInertiaDecomposition_of_normKernel
    rationalNormKernelFiniteRestriction.{uF, uV}
    rationalNormKernelTwistEquivalence.{uF, uV, uV}

end Langlands.CuspidalSupport
