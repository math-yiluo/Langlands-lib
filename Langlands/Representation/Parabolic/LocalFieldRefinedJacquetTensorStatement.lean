import Langlands.AllField.Representation.Geometric.RefinementFunctors
import Langlands.AllField.Representation.Jacquet.Parabolic
import Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor

/-! Upper normalized Jacquet restriction of a tensor product inside a matrix Levi. -/

namespace Langlands.RefinedJacquetTensor

open GeneralLinear Geometric

universe uF uV

/-- The normalized Jacquet module of an external tensor in a product Levi
identifies with the external tensor of the normalized factor Jacquet modules.
The comparison acts by the quotient maps in each tensor slot. -/
def LocalFieldRefinedJacquetTensorStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) (B : BlockShape n)
    (S : BlockRefinement B) (A : ∀ i, Rep.{uV} ℂ (GeneralLinear (B.size i) F)),
    Nonempty {e : Representation.Equiv
        (T.normalizedRefinedJacquet B S (FiniteTensor.external fun i => (A i).ρ))
        ((FiniteTensor.external fun i => T.normalizedJacquet (S i) (A i).ρ).comp
          (refinedLeviEquiv F B S).symm.toMonoidHom) //
      ∀ v : ∀ i, A i,
        e (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v)) =
          PiTensorProduct.tprod ℂ (fun i => (S i).jacquetMk (A i).ρ (v i))}

end Langlands.RefinedJacquetTensor
