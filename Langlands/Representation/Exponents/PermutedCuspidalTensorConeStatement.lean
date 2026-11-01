import Langlands.Representation.Exponents.SquareIntegrableActualJacquetConeStatement
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.Induction.BlockFactors

/-! # The same scalar coordinates on every actually occurring permuted tensor -/

namespace Langlands

universe uF uV

/-- Original factor characters and their original real coordinates give the
permuted coordinate vector on any actual permuted tensor Jacquet occurrence. -/
def PermutedCuspidalTensorConeStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : GeneralLinear.BlockShape n)
      (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      T.IsSquareIntegrable π.representation →
      ∀ (C : ∀ i, GeneralLinear.SupercuspidalRep.{uF,uV}
        (F := F.Carrier) (n := B.size i))
        (c : Fin B.length → (F.Carrierˣ →* ℂˣ))
        (x : Fin B.length → ℝ),
        (∀ i, Classification.HasScalarCharacter (C i).obj.representation
          GeneralLinear.scalar (c i)) →
        (∀ i (a : F.Carrierˣ), ‖(c i a : ℂ)‖ =
          T.normalizedAbs (a : F.Carrier) ^ (x i)) →
        ∀ e : Equiv.Perm (Fin B.length),
          SmoothRep.IsSubquotient
            (FiniteTensor.externalSmoothObject (fun i => (C (e i)).obj))
            ((T.normalizedJacquetFunctor (B.permute e)).obj π) →
          Exponents.IsPositiveRootCone (x ∘ e)

end Langlands
