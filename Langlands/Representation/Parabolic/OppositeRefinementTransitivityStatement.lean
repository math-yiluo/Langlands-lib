import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

/-! Pointwise normalized transitivity for the actual opposite Jacquet quotients. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- Taking the actual outer and then inner opposite coinvariants agrees
equivariantly with taking the actual full composed opposite coinvariants.
The equivalence sends the iterated class of each vector to its direct class. -/
def NormalizedOppositeRefinementTransitivityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
    let O := CuspidalJacquetMultiplicity.oppositeJacquet T B A
    ∃ E : (T.normalizedRefinedOppositeJacquet B S O.ρ).Equiv
        (T.normalizedComposedOppositeJacquet B S A.ρ),
      ∀ v : A,
        E (refinedOppositeJacquetMk B S O.ρ
          (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v)) =
            composedOppositeJacquetMk B S A.ρ v

end Langlands.Parabolic
