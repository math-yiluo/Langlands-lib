import Langlands.Automorphic.CuspidalBandMixedMultiplicityOneReduction
import Langlands.Automorphic.CuspidalBandMixedWhittakerUniqueness
import Langlands.Representation.Archimedean.UnitaryWhittakerMultiplicityOneProof

/-! # Multiplicity one for actual cuspidal operator realizations -/

set_option autoImplicit false

namespace Langlands.Automorphic

universe u

/-- Equivalent actual cuspidal operator realizations have the same subspace
of automorphic functions. -/
theorem cuspidalOperatorMultiplicityOne : CuspidalOperatorMultiplicityOneStatement.{u} :=
  cuspidalOperatorMultiplicityOne_of_bandMixed.{u}
    (cuspidalBandMixedWhittakerUniquenessFromLocal.{u}
      Langlands.Archimedean.unitaryWhittakerMultiplicityOne.{u})

end Langlands.Automorphic
