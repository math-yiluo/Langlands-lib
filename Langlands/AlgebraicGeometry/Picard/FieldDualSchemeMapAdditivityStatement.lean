import Langlands.AlgebraicGeometry.Picard.DualSchemeMapTensor
import Langlands.AlgebraicGeometry.Picard.HomPicardZeroPullbackProof

/-! # Additivity of the actual dual scheme maps over a field -/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AbelianScheme

open Langlands.Scheme.Modules

/-- Dualization carries addition of homomorphisms to the constructed tensor
multiplication on the chosen dual parameter scheme. -/
def FieldDualSchemeMapAdditivityStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (k : Type u) [Field k]
    (A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A) (hB : HasDualScheme B) (f g : A ⟶ B),
    dualSchemeMap homPicardZeroPullback (f + g) hA hB =
      prod.lift (dualSchemeMap homPicardZeroPullback f hA hB)
        (dualSchemeMap homPicardZeroPullback g hA hB) ≫
          dualTensor stability A hA preservation

end Langlands.AbelianScheme
