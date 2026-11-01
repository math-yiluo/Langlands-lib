import Langlands.Representation.GodementJacquet.ModelWhittakerRationalityProof
import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.Representation.GodementJacquet.UniformWhittakerMatrixConvergence

/-!
# Ordinary matrix analytic data on actual Whittaker models

Per-pair rationality, a common convergence bound and a normalized generator
are assembled on the actual coefficient image. The uniform Mellin input
is explicit.
-/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

local instance (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- Every actual bi-smooth coefficient has a shifted rational value in the
Whittaker ideal of the original representation and specified functional. -/
theorem exists_modelMatrixRationalValue
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (Φ : MatrixTestFunction n F.Carrier)
    (f : biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ)) :
    ∃ R : RationalFunctions,
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n)
        Φ f.val R ∧ R ∈ jpssI3 F ψ σ ℓ := by
  apply exists_hasShiftedRationalValue_mem_of_generators (f := f)
  intro Λ w
  obtain ⟨R, hRmem, hR⟩ := exists_mem_jpssI3_of_coefficient F ψ σ hσ.1.1 ℓ
    (glModel_isAdmissible F ψ σ ℓ hσ.1)
    (modelWhittakerRationality p F ψ n σ hσ ℓ hℓ)
    Λ w.val (biSmoothCoefficient _ Λ w) (biSmoothCoefficient_apply _ Λ w) Φ
  exact ⟨R, hR, hRmem⟩

/-- Choose an actual shifted rational continuation for each full-matrix test
and coefficient of the specified actual Whittaker model. -/
def modelMatrixRationalValue
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (Φ : MatrixTestFunction n F.Carrier)
    (f : biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ)) : RationalFunctions :=
  (exists_modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f).choose

/-- The chosen rational value is a continuation of the actual integral and
belongs to the original Whittaker ideal. -/
theorem modelMatrixRationalValue_spec
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (Φ : MatrixTestFunction n F.Carrier)
    (f : biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ)) :
    HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n)
        Φ f.val (modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f) ∧
      modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f ∈ jpssI3 F ψ σ ℓ :=
  (exists_modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f).choose_spec

/-- The chosen polynomial supplies the entire ordinary analytic predicate
on every nonzero actual coefficient model, under uniform Mellin convergence. -/
theorem modelMatrixAnalyticAssertions
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    MatrixAnalyticAssertions F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) (modelMatrixLPolynomial F ψ σ ν hσ) := by
  refine ⟨WhittakerTorus.Padic.glModel_matrixConvergesOnRight F hU ψ σ hσ ℓ, ?_,
    modelMatrixLPolynomial_normalized F ψ σ ν hσ ℓ hℓ⟩
  intro Φ f
  exact ⟨modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f,
    (modelMatrixRationalValue_spec F ψ σ hσ ℓ hℓ Φ f).1⟩

/-- One polynomial retains the complete symmetric pair certificate and
works in the ordinary analytic predicate for every nonzero functional. -/
theorem exists_modelMatrixAnalyticAssertions
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ P : Polynomial ℂ,
      IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter 1) P ∧
      ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
        MatrixAnalyticAssertions F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) P :=
  ⟨modelMatrixLPolynomial F ψ σ ν hσ, modelMatrixLPolynomial_pair F ψ σ ν hσ,
    fun ℓ hℓ => modelMatrixAnalyticAssertions F ψ σ hU ν hσ ℓ hℓ⟩

end Langlands.GodementJacquet.Padic
