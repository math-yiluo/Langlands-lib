import Langlands.Representation.Whittaker.InducedStatement
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Jacquet.Localization

/-! # Character-localized heredity for upper block induction

This proposition is a derived quotient formulation of Whittaker heredity.
It is a statement target, not a proof of heredity.
-/

namespace Langlands

universe uF uV

/-- The actual character quotient of upper unnormalized smooth induction is
linearly equivalent to the finite tensor of the block character quotients. -/
def InducedLocalizationStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)),
      letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
      ∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
        (ψ : AddChar F.Carrier ℂ),
        Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
        (∀ i, IsAdmissible (π i)) →
        (∀ i, Module.Finite (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier))
          (π i).asModule) →
        let induced := Induction.smoothInduced (B.parabolic F.Carrier)
          ((FiniteTensor.external π).comp (B.leviProjection F.Carrier))
        Nonempty
          (Jacquet.Localization.Coinvariants induced
              (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
              (Whittaker.entrywiseCharacter ψ (n + 1)) ≃ₗ[ℂ]
            PiTensorProduct ℂ (fun i : Fin B.length =>
              Jacquet.Localization.Coinvariants (π i)
                (GeneralLinear.upperUnipotent (B.size i) F.Carrier)
                (Whittaker.entrywiseCharacter ψ (B.size i))))

end Langlands
