import Langlands.Representation.Exponents.DualJacquet
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-! The actual refined opposite dual spectrum of a Jacquet subquotient
is contained in the flattened opposite dual spectrum of the source.
This file only specifies that algebraic inheritance obligation. -/

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW

/-- Refined opposite Jacquet eigenfunctionals of an arbitrary actual
subquotient occur in the flattened opposite dual spectrum of the source.
There is no irreducibility or scalar-character hypothesis on the subquotient. -/
def GLOppositeJacquetSubquotientExponentInheritanceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (C : BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → IsAdmissible A.ρ →
      ∀ S : Rep.{uW} ℂ (C.Levi F.Carrier),
        (∃ U : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ,
          ∃ q : U.toRepresentation.IntertwiningMap S.ρ, Function.Surjective q) →
        ∀ (D : BlockRefinement C)
          (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ)
          (φ : Module.Dual ℂ (RefinedOppositeJacquetModule C D S.ρ)),
          IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
          φ ≠ 0 →
          (∀ (a : Fin (C.flatten D).length → F.Carrierˣ) (v : S),
            φ (T.normalizedRefinedOppositeJacquet C D S.ρ
                (flattenedLeviEquiv F.Carrier C D
                  ((C.flatten D).blockScalarLevi F.Carrier a))
                (refinedOppositeJacquetMk C D S.ρ v)) =
              (ψ a : ℂ) * φ (refinedOppositeJacquetMk C D S.ρ v)) →
          T.IsDualJacquetExponent (C.flatten D) A ψ

end Langlands
