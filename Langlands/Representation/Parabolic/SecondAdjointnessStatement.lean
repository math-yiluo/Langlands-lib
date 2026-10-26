import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-!
# Actual normalized second adjointness

Admissible standard GL and refined product-Levi second adjointness, with
naturality for the actual induced and quotient maps. These are statements.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV uW

/-- Standard GL second adjointness, natural in both admissible representations. -/
def StandardSecondAdjointnessClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n),
      ∃ E : ∀ (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
          (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier)),
          IsAdmissible σ.ρ → IsAdmissible π.ρ →
          ((T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ) ≃ₗ[ℂ]
            (σ.ρ.IntertwiningMap (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ),
        (∀ (σ σ' : Rep.{uV} ℂ (B.Levi F.Carrier))
          (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
          (hσ : IsAdmissible σ.ρ) (hσ' : IsAdmissible σ'.ρ)
          (hπ : IsAdmissible π.ρ) (a : σ'.ρ.IntertwiningMap σ.ρ)
          (f : (T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ)
          (v : σ'),
          E σ' π hσ' hπ (f.comp (T.normalizedParabolicInducedMap B a)) v =
            E σ π hσ hπ f (a v)) ∧
        (∀ (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
          (π π' : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
          (hσ : IsAdmissible σ.ρ) (hπ : IsAdmissible π.ρ)
          (hπ' : IsAdmissible π'.ρ) (b : π.ρ.IntertwiningMap π'.ρ)
          (f : (T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ)
          (v : σ),
          E σ π' hσ hπ' (b.comp f) v =
            Jacquet.map (B.oppositeUnipotentSubgroup F.Carrier)
              (B.leviSubgroup F.Carrier)
              (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
              b (E σ π hσ hπ f v))

/-- Second adjointness inside a product Levi, with no tensor-product restriction. -/
def RefinedSecondAdjointnessClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B),
      ∃ E : ∀ (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
          (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
          IsAdmissible σ.ρ → IsAdmissible π.ρ →
          ((T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ) ≃ₗ[ℂ]
            (σ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)),
        (∀ (σ σ' : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
          (π : Rep.{uW} ℂ (B.Levi F.Carrier))
          (hσ : IsAdmissible σ.ρ) (hσ' : IsAdmissible σ'.ρ)
          (hπ : IsAdmissible π.ρ) (a : σ'.ρ.IntertwiningMap σ.ρ)
          (f : (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ)
          (v : σ'),
          E σ' π hσ' hπ (f.comp (T.normalizedRefinedInducedMap B S a)) v =
            E σ π hσ hπ f (a v)) ∧
        (∀ (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
          (π π' : Rep.{uW} ℂ (B.Levi F.Carrier))
          (hσ : IsAdmissible σ.ρ) (hπ : IsAdmissible π.ρ)
          (hπ' : IsAdmissible π'.ρ) (b : π.ρ.IntertwiningMap π'.ρ)
          (f : (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ)
          (v : σ),
          E σ π' hσ hπ' (b.comp f) v =
            T.normalizedRefinedOppositeJacquetMap B S b (E σ π hσ hπ f v))

/-- The complete admissible second-adjointness interface for the actual functors. -/
def NormalizedSecondAdjointnessStatement : Prop :=
  StandardSecondAdjointnessClause.{uF, uV, uW} ∧
    RefinedSecondAdjointnessClause.{uF, uV, uW}

end Langlands.Parabolic
