import Langlands.AlgebraicGeometry.ImmersionExhaustionStalkLocality
import Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionInduction
import Langlands.GroupScheme.ArtinianUniformExponentProof
import Langlands.GroupScheme.UniformExponentReduction

/-! # Uniform exponent for quasi-finite commutative group schemes -/

universe u

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.ImmersionExhaustion

/-- SGA 3, Exposé IX, Lemma 6.1. -/
theorem quasiFiniteCommutativeUniformExponent :
    QuasiFiniteCommutativeUniformExponentStatement.{u} := by
  have stalkLocality : StalkLocalityStatement.{u, 0} := by
    intro S _ I _ _ _ D hft hqc h
    exact Family.full_of_stalk_full D hft hqc h
  exact UniformExponentReduction.reduction ArtinianUniformExponent.artinianUniformExponent
    (exhaustion_of_stalkLocality stalkLocality)

end Langlands.GroupScheme
