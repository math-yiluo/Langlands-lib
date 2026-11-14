import Langlands.Representation.Whittaker.InducedLocalizationStatement
import Langlands.AllField.Representation.Whittaker.InducedStatement
/-! # Character-localized heredity for upper block induction

This proposition is a derived quotient formulation of Whittaker heredity.
It is a statement target, not a proof of heredity.
-/

namespace Langlands.AllField

universe uF uV

/-- The actual character quotient of upper unnormalized smooth induction is
linearly equivalent to the finite tensor of the block character quotients. -/
def InducedLocalizationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)),
      letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
      ∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
        (ψ : AddChar F ℂ),
        Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
        (∀ i, IsAdmissible (π i)) →
        (∀ i, Module.Finite (MonoidAlgebra ℂ (GeneralLinear (B.size i) F))
          (π i).asModule) →
        let induced := Induction.smoothInduced (B.parabolic F)
          ((FiniteTensor.external π).comp (B.leviProjection F))
        Nonempty
          (Jacquet.Localization.Coinvariants induced
              (GeneralLinear.upperUnipotent (n + 1) F)
              (Whittaker.entrywiseCharacter ψ (n + 1)) ≃ₗ[ℂ]
            PiTensorProduct ℂ (fun i : Fin B.length =>
              Jacquet.Localization.Coinvariants (π i)
                (GeneralLinear.upperUnipotent (B.size i) F)
                (Whittaker.entrywiseCharacter ψ (B.size i))))

end Langlands.AllField
