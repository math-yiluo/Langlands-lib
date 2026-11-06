import Langlands.GroupScheme.SimplyConnected.DerivedCoverTorusProductSmoothReduction
import Langlands.GroupScheme.SimplyConnected.DerivedCoverMaximalTorusPreimageProof
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityProof

/-! # Smoothness of derived-cover and maximal-torus multiplication -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, multiplication from a simply connected cover of the
derived subgroup and a maximal torus is a smooth morphism of schemes. -/
theorem derivedCoverTorusProductSmooth :
    DerivedCoverTorusProductSmoothStatement.{u} :=
  derivedCoverTorusProductSmooth_of_preimage_of_surjectivity
    derivedCoverMaximalTorusPreimage derivedMaximalTorusProductSurjectivity

end Langlands.GroupScheme
