import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.Representation.GodementJacquet.CoefficientTransport

/-!
# Transport on actual coefficient models

Evaluation recovers the same coefficient subrepresentation when applied to a
coefficient model. Nonzero functionals of a full Whittaker-type representation
have equivalent actual models and the same normalized matrix equation data.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uG uV uW uF

section Evaluation

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {N : Subgroup G} {θ : N →* ℂˣ}
  (π : Representation ℂ G V) (ℓ : functionals N θ π)

/-- The coefficient map for evaluation on a coefficient model is its inclusion
into the ambient equivariant function space. -/
theorem coefficientMap_coefficientModelEvaluation
    (w : (coefficientModel π ℓ).toSubmodule) :
    coefficientMap (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ)
      (coefficientModelEvaluation π ℓ) w = w.val := by
  apply Subtype.ext
  funext g
  change w.val.val (1 * g) = w.val.val g
  rw [one_mul]

/-- Taking the coefficient model with evaluation on the original coefficient
image recovers exactly that image, as an actual subrepresentation. -/
theorem coefficientModel_coefficientModelEvaluation :
    coefficientModel (V := (coefficientModel π ℓ).toSubmodule)
      (modelRepresentation π ℓ) (coefficientModelEvaluation π ℓ) =
        coefficientModel π ℓ := by
  apply Subrepresentation.toSubmodule_injective
  ext f
  change (∃ w : (coefficientModel π ℓ).toSubmodule,
    coefficientMap (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ)
      (coefficientModelEvaluation π ℓ) w = f) ↔ f ∈ (coefficientModel π ℓ).toSubmodule
  constructor
  · rintro ⟨w, rfl⟩
    rw [coefficientMap_coefficientModelEvaluation]
    exact w.property
  · intro hf
    exact ⟨⟨f, hf⟩, coefficientMap_coefficientModelEvaluation π ℓ ⟨f, hf⟩⟩

/-- Evaluation on a nonzero functional's coefficient image is nonzero. -/
theorem coefficientModelEvaluation_ne_zero (hℓ : ℓ.val ≠ 0) :
    (coefficientModelEvaluation π ℓ).val ≠ 0 := by
  intro h
  apply hℓ
  have he : coefficientModelEvaluation π ℓ = 0 := Subtype.ext h
  have hL : ℓ = 0 := by
    rw [← coefficientModelEvaluation_comap π ℓ, he, map_zero]
  exact congrArg Subtype.val hL

end Evaluation

section ModelEquivalences

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}

/-- The actual models of two nonzero functionals are equivalent by the identity
on their underlying functions; the original representation need not be
equivalent to either model. -/
def nonzeroFunctionalModelEquiv
    (hπ : IsOfWhittakerType n θ π)
    (ℓ ℓ' : functionals (upperUnipotent (n + 1) F) θ π)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    (modelRepresentation π ℓ).Equiv (modelRepresentation π ℓ') :=
  Representation.Equiv.mk
    (LinearEquiv.ofEq (coefficientModel π ℓ).toSubmodule
      (coefficientModel π ℓ').toSubmodule
      (congrArg Subrepresentation.toSubmodule
        (coefficientModel_eq_of_whittakerType hπ hℓ hℓ')))
    (fun _ => by ext w; rfl)

end ModelEquivalences

end Langlands.RankinSelberg

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV uW

section MatrixData

variable {F : Type uF} [Field F] [TopologicalSpace F]
  [MeasurableSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {ν : AdditiveHaarMeasure F}
  {abv : AbsoluteValue F ℝ} {μ : Measure (Langlands.GeneralLinear (n + 1) F)}
  {P PDual : Polynomial ℂ} {c : ℂˣ} {m : ℤ}

/-- An actual representation equivalence preserves all normalized matrix
functional-equation data, including the supplied scalar Fourier measure. -/
theorem normalizedMatrixFunctionalEquationData_equiv (e : σ.Equiv τ) :
    NormalizedMatrixFunctionalEquationData q ψ ν abv μ σ P PDual c m ↔
      NormalizedMatrixFunctionalEquationData q ψ ν abv μ τ P PDual c m := by
  unfold NormalizedMatrixFunctionalEquationData
  rw [matrixAnalyticAssertions_equiv q abv μ e P,
    iotaMatrixAnalyticAssertions_equiv q abv μ e PDual,
    biSmoothMatrixCoefficients_equiv e]

end MatrixData

end Langlands.GodementJacquet

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section PadicData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixComparisonTransportTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matrixComparisonTransportMeasurable : MeasurableSpace F.Carrier :=
  borel F.Carrier

/-- The supplied actual normalized matrix equation on a full Whittaker-type
model is independent of its chosen nonzero standard functional. -/
theorem normalizedMatrixData_nonzero_functional_iff
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ ℓ' : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ) :
    GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
        (V := (glCoefficientModel ψ n π ℓ).toSubmodule)
        (glModelRepresentation ψ n π ℓ) P PDual c m ↔
      GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
        (V := (glCoefficientModel ψ n π ℓ').toSubmodule)
        (glModelRepresentation ψ n π ℓ') P PDual c m := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  exact GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
    (nonzeroFunctionalModelEquiv hπ ℓ ℓ' hℓ hℓ')

end PadicData

end Langlands.RankinSelberg
