import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Natural same-parabolic normalized induction duality

Coherent duality families for actual standard GL and refined product-Levi
induction. These proposition definitions impose naturality on actual maps.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- Smooth duality commutes naturally with standard normalized induction. -/
def StandardNaturalInductionDualityClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      ∃ E : ∀ (σ : Rep.{uV} ℂ (B.Levi F.Carrier)), IsAdmissible σ.ρ →
          Representation.Equiv
            (smoothContragredient (T.normalizedParabolicInduced B σ.ρ))
            (T.normalizedParabolicInduced B (smoothContragredient σ.ρ)),
        ∀ (σ τ : Rep.{uV} ℂ (B.Levi F.Carrier))
          (hσ : IsAdmissible σ.ρ) (hτ : IsAdmissible τ.ρ)
          (a : σ.ρ.IntertwiningMap τ.ρ)
          (ℓ : SmoothDual (T.normalizedParabolicInduced B τ.ρ)),
          E σ hσ (contragredientMap (T.normalizedParabolicInducedMap B a) ℓ) =
            T.normalizedParabolicInducedMap B (contragredientMap a) (E τ hτ ℓ)

/-- The same natural duality for arbitrary refined product-Levi inputs. -/
def RefinedNaturalInductionDualityClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
      letI := T.leviTopologicalGroup B
      ∃ E : ∀ (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)), IsAdmissible σ.ρ →
          Representation.Equiv
            (smoothContragredient (T.normalizedRefinedInduced B S σ.ρ))
            (T.normalizedRefinedInduced B S (smoothContragredient σ.ρ)),
        ∀ (σ τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
          (hσ : IsAdmissible σ.ρ) (hτ : IsAdmissible τ.ρ)
          (a : σ.ρ.IntertwiningMap τ.ρ)
          (ℓ : SmoothDual (T.normalizedRefinedInduced B S τ.ρ)),
          E σ hσ (contragredientMap (T.normalizedRefinedInducedMap B S a) ℓ) =
            T.normalizedRefinedInducedMap B S (contragredientMap a) (E τ hτ ℓ)

/-- Natural standard and refined same-parabolic normalized induction duality. -/
def NaturalNormalizedInductionDualityStatement : Prop :=
  StandardNaturalInductionDualityClause.{uF, uV} ∧
    RefinedNaturalInductionDualityClause.{uF, uV}

end Langlands.Parabolic
