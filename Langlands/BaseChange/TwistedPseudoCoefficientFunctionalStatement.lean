import Langlands.BaseChange.TwistedPaleyWiener

/-! # A spectral functional with the prescribed pseudo-coefficient values -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

/-- The functional construction in Henniart–Lemaire II.5.13, before applying the twisted
trace Paley–Wiener theorem. For ranks at least two, the functional has the prescribed
pseudo-coefficient values, is compactly dominated, and is regular on all induced families.
It is the input to trace realization. -/
def TwistedPseudoCoefficientFunctionalExistenceStatement.{u, v, z} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 2 ≤ n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      IsSigmaDiscreteSeries σ n τ →
      ∀ χ : Subgroup.center (GeneralLinear n E) →* ℂˣ, HasCentralCharacterRep τ χ →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        ∃ Φ : Module.Dual ℂ (Distribution (GeneralLinear n E)),
          IsCompactlyDominatedFunctional.{v, z} (entrywiseAut σ n) μ Φ ∧
          IsSigmaInducedRegularFunctional.{u, v, z} σ μ Φ ∧
          Φ (twistedDistribution μ τ hτ A.toLinearMap) = 1 ∧
          ∀ (W' : Type z) [AddCommGroup W'] [Module ℂ W']
            (τ' : Representation ℂ (GeneralLinear n E) W') (hτ' : IsAdmissible τ'),
            τ'.IsIrreducible → IsTemperedRep τ' → HasCentralCharacterRep τ' χ →
            IsEmpty (τ'.Equiv τ) → ∀ A' : SigmaIntertwiner σ n τ',
              Φ (twistedDistribution μ τ' hτ' A'.toLinearMap) = 0

end Langlands.BaseChange
