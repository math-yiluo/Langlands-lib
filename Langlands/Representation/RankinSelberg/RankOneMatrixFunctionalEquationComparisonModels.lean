import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.Whittaker.Transport
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-!
# Coefficient-model hypotheses and gamma-equation uniformity

The coefficient image of a full Whittaker-type representation again has full
Whittaker type. A gamma equation at the constructed quotient measure for one
nonzero functional pair transports to every compatible measure and nonzero pair.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW uG

section Algebraic

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {N : Subgroup G} {θ : N →* ℂˣ}
  (π : Representation ℂ G V) (ℓ : functionals N θ π)

/-- Evaluation at the identity on the actual coefficient image. -/
def coefficientModelEvaluation :
    functionals N θ (V := (coefficientModel π ℓ).toSubmodule)
      (modelRepresentation π ℓ) :=
  evaluationFunctional (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ)
    { toLinearMap := (coefficientModel π ℓ).toSubmodule.subtype
      isIntertwining' _ := rfl }

/-- Evaluation on the image pulls back to the original functional. -/
theorem coefficientModelEvaluation_comap :
    functionalsComap (W := (coefficientModel π ℓ).toSubmodule)
      (modelMap π ℓ) (coefficientModelEvaluation π ℓ) = ℓ := by
  apply Subtype.ext
  ext v
  change ℓ.val (π 1 v) = ℓ.val v
  rw [map_one, Module.End.one_apply]

/-- Finite generation over the group algebra descends to the coefficient image. -/
theorem coefficientModel_isFinite
    (hπ : Module.Finite (MonoidAlgebra ℂ G) π.asModule) :
    Module.Finite (MonoidAlgebra ℂ G) (modelRepresentation π ℓ).asModule := by
  let := hπ
  exact Module.Finite.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule π
      (modelRepresentation π ℓ) (modelMap π ℓ))
    (modelMap_surjective π ℓ)

end Algebraic

section Models

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}

/-- Pullback identifies the model's entire functional space with that of the
original full Whittaker-type representation, without assuming irreducibility. -/
def coefficientModelFunctionalsEquiv
    (hπ : IsOfWhittakerType n θ π)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ π) (hℓ : ℓ.val ≠ 0) :
    functionals (upperUnipotent (n + 1) F) θ
      (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ) ≃ₗ[ℂ]
      functionals (upperUnipotent (n + 1) F) θ π := by
  apply LinearEquiv.ofBijective
    (functionalsComap (W := (coefficientModel π ℓ).toSubmodule) (modelMap π ℓ))
  constructor
  · intro L M h
    apply Subtype.ext
    ext w
    obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ w
    exact congrArg (fun t : functionals (upperUnipotent (n + 1) F) θ π =>
      t.val v) h
  · intro L
    obtain ⟨c, rfl⟩ := hπ.eq_smul hℓ L
    refine ⟨c • coefficientModelEvaluation π ℓ, ?_⟩
    rw [map_smul, coefficientModelEvaluation_comap]

/-- Full Whittaker type descends to the actual coefficient image when compact
open subgroups are cofinal among open subgroups. -/
theorem coefficientModel_isOfWhittakerType
    (hcofinal : ∀ H : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
        IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)) ∧ K ≤ H)
    (hπ : IsOfWhittakerType n θ π)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ π) (hℓ : ℓ.val ≠ 0) :
    IsOfWhittakerType n θ (V := (coefficientModel π ℓ).toSubmodule)
      (modelRepresentation π ℓ) := by
  refine ⟨Unramified.SphericalExistence.isAdmissible_of_surjective hcofinal
      (W := (coefficientModel π ℓ).toSubmodule) (modelMap π ℓ)
      (modelMap_surjective π ℓ) hπ.1,
    coefficientModel_isFinite π ℓ hπ.2.1, ?_⟩
  obtain ⟨e⟩ := hπ.2.2
  exact ⟨(coefficientModelFunctionalsEquiv hπ ℓ hℓ).trans e⟩

end Models

section PadicModels

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixComparisonModelsTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The canonical p-adic coefficient model has all three full Whittaker-type
hypotheses required in the matrix-to-rank-one comparison. -/
theorem glCoefficientModel_isOfWhittakerType
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    IsOfWhittakerType n (standardCharacter ψ n)
      (V := (glCoefficientModel ψ n π ℓ).toSubmodule)
      (glModelRepresentation ψ n π ℓ) := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact coefficientModel_isOfWhittakerType
    (Unramified.SphericalExistence.exists_compactOpenSubgroup_le F) hπ ℓ hℓ

end PadicModels

section Uniformity

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {G : RationalFunctions}

/-- One equal-rank gamma equation at the constructed quotient measure supplies
the full relation, with the same rational gamma function. -/
theorem equalRankGammaFactor_of_equation
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hFE : EqualRankGammaEquation q ψ abv (unipotentQuotientHaar F n) ν
      π σ ℓ ℓ' G) :
    IsEqualRankGammaFactor q ψ abv ν π σ G := by
  refine ⟨⟨unipotentHaar_isMulRightInvariant F n, unipotent_compatibleMeasureExists F n⟩,
    ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, ?_⟩
  intro hinv μ hμ ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  rw [unipotentQuotientHaar_unique F n μ hμ]
  exact (EqualRankGammaEquation.congr_model
    (coefficientModel_eq_of_whittakerType hπ hℓ hℓ₂)
    (coefficientModel_eq_of_whittakerType hσ hℓ' hℓ₂')).mp hFE

/-- The full unequal-rank equation transports across all compatible quotient
measures and all nonzero functional pairs without changing its gamma function. -/
theorem unequalRankGammaFactor_of_equation
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (hnr : n < r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hFE : UnequalRankGammaEquation hnr q ψ abv (unipotentQuotientHaar F n) ν
      π σ ℓ ℓ' G) :
    IsUnequalRankGammaFactor hnr q ψ abv ν π σ G := by
  refine ⟨⟨unipotentHaar_isMulRightInvariant F n, unipotent_compatibleMeasureExists F n⟩,
    ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, ?_⟩
  intro hinv μ hμ ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  rw [unipotentQuotientHaar_unique F n μ hμ]
  exact (UnequalRankGammaEquation.congr_model
    (coefficientModel_eq_of_whittakerType hπ hℓ hℓ₂)
    (coefficientModel_eq_of_whittakerType hσ hℓ' hℓ₂')).mp hFE

end Uniformity

end Langlands.RankinSelberg
