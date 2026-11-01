import Langlands.Representation.RankinSelberg.GammaModelInclusion
import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonProof
import Langlands.Representation.Whittaker.ModelGenericSocleProof
import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionProof

/-!
# Gamma comparison for an actual subrepresentation of a coefficient model

The original representation can be reducible. An ambient matrix functional
equation supplies the specified gamma expression on a subrepresentation of its
coefficient model. Existence of a gamma certificate on the original remains a
separate premise.
-/

noncomputable section

namespace Langlands.Whittaker

universe uG uV

variable {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ G V) (ℓ : functionals N θ π)

local instance submodelComparisonCoefficientGroup : AddCommGroup (coefficientModel π ℓ).toSubmodule :=
  (coefficientModel π ℓ).toSubmodule.addCommGroup

variable (S : Subrepresentation (modelRepresentation π ℓ))

/-- The actual inclusion of a subrepresentation of a coefficient image into
the ambient equivariant function representation. -/
def submodelFunctionMap :
    S.toRepresentation.IntertwiningMap (functionRepresentation N θ) where
  toLinearMap :=
    (coefficientModel π ℓ).toSubmodule.subtype.comp S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- Evaluation at the identity on the actual functions in the subrepresentation. -/
def submodelEvaluation : functionals N θ (V := S.toSubmodule) S.toRepresentation :=
  evaluationFunctional (V := S.toSubmodule) S.toRepresentation (submodelFunctionMap π ℓ S)

theorem submodelFunctionMap_injective :
    Function.Injective (submodelFunctionMap π ℓ S) := by
  intro v w h
  exact Subtype.ext (Subtype.ext h)

/-- Its coefficient map recovers the unchanged underlying equivariant function. -/
theorem coefficientMap_submodelEvaluation (v : S.toSubmodule) :
    coefficientMap (V := S.toSubmodule) S.toRepresentation
      (submodelEvaluation π ℓ S) v = v.val.val := by
  apply Subtype.ext
  funext g
  change v.val.val.val (1 * g) = v.val.val.val g
  rw [one_mul]

/-- The evaluation coefficient image is contained in the original coefficient
image, without identifying the original representation with that image. -/
theorem coefficientModel_submodelEvaluation_le :
    coefficientModel (V := S.toSubmodule) S.toRepresentation (submodelEvaluation π ℓ S) ≤
      coefficientModel π ℓ := by
  rintro f ⟨v, rfl⟩
  change coefficientMap (V := S.toSubmodule) S.toRepresentation
    (submodelEvaluation π ℓ S) v ∈ coefficientModel π ℓ
  rw [coefficientMap_submodelEvaluation]
  exact v.val.property

/-- Every nonzero invariant subspace of a coefficient model has nonzero
evaluation functional. -/
theorem submodelEvaluation_ne_zero (hS : S ≠ ⊥) :
    (submodelEvaluation π ℓ S).val ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_subrepresentation_ne_bot S hS
  exact evaluationFunctional_ne_zero (X := S.toSubmodule) S.toRepresentation
    (submodelFunctionMap π ℓ S)
    (submodelFunctionMap_injective π ℓ S) hv

end Langlands.Whittaker

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

section PadicComparison

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance submodelComparisonTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance submodelComparisonValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance submodelComparisonLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance submodelComparisonMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance submodelComparisonBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance submodelComparisonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance submodelComparisonDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance submodelComparisonGLCoefficientGroup {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n π) : AddCommGroup (glCoefficientModel ψ n π ℓ).toSubmodule :=
  (glCoefficientModel ψ n π ℓ).toSubmodule.addCommGroup

/-- A nonzero subrepresentation of the actual coefficient model has the same
gamma expression against the trivial rank-one test whenever both complete
certificates already exist. No irreducibility is required. -/
theorem gamma_eq_submodel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0)
    (S : Subrepresentation (glModelRepresentation ψ n π ℓ)) (hS : S ≠ ⊥)
    {G GS : RationalFunctions}
    (h : IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G)
    (hSgamma : IsPadicSymmetricGammaFactor F ψ ν (V := S.toSubmodule) S.toRepresentation
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) GS) : G = GS := by
  let := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (0 + 1) F.Carrier)
  let : BorelSpace (GeneralLinear.upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  rw [isPadicSymmetricGammaFactor_of_le (Nat.zero_le n)] at h hSgamma
  have htest : ∃ ℓ' : glInverseFunctionals ψ 0
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)), ℓ'.val ≠ 0 := by
    by_cases hn : n = 0
    · subst n
      exact (isPairGammaFactor_self.mp hSgamma).2.2.1
    · exact ((isPairGammaFactor_of_lt (Nat.pos_of_ne_zero hn)).mp hSgamma).2.2.1
  obtain ⟨ℓ', hℓ'⟩ := htest
  exact (IsPairGammaFactor.eq_of_model_le
    (PadicField.TopologicalData.residueCardinality_gt_one _)
    (submodelEvaluation_ne_zero π ℓ S hS) hℓ' hℓ hℓ'
    (coefficientModel_submodelEvaluation_le π ℓ S) le_rfl hSgamma h).symm

/-- The actual subquotient map into a submodel supplies the coefficient
inclusion needed by the ambient matrix comparison. The resulting expression
is the original representation's gamma factor, provided a complete gamma
certificate on the original exists. Normalized matrix generators stay on the
ambient representation. -/
theorem gamma_of_submodel_ambient_matrix
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0)
    (S : Subrepresentation (glModelRepresentation ψ n π ℓ)) (hS : S ≠ ⊥)
    (hStype : IsOfWhittakerType (V := S.toSubmodule) n (standardCharacter ψ n)
      S.toRepresentation)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hρ : Langlands.IsSmooth ρ) (A : Subrepresentation ρ)
    (f : A.toRepresentation.IntertwiningMap S.toRepresentation) (hf : Function.Surjective f)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      ρ P PDual c a)
    (hexists : ∃ G, IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G) :
    IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual) := by
  let ev := submodelEvaluation π ℓ S
  let q := (modelMap (V := S.toSubmodule) S.toRepresentation ev).comp f
  have hq : Function.Surjective q :=
    (modelMap_surjective (V := S.toSubmodule) S.toRepresentation ev).comp hf
  have hcoeff := GodementJacquet.Padic.subquotientCoefficientInclusion
    p F n W (coefficientModel (V := S.toSubmodule) S.toRepresentation ev).toSubmodule
    ρ (modelRepresentation (V := S.toSubmodule) S.toRepresentation ev) hρ A q hq
  have hSgamma := rankOneAmbientMatrixFunctionalEquationComparison
    p F ψ ν hν n S.toSubmodule S.toRepresentation hStype
    ev (submodelEvaluation_ne_zero π ℓ S hS) W ρ hcoeff P PDual c a hdata
  obtain ⟨G, hG⟩ := hexists
  obtain rfl := gamma_eq_submodel F ψ ν π ℓ hℓ S hS hG hSgamma
  exact hG

end PadicComparison

end Langlands.RankinSelberg
