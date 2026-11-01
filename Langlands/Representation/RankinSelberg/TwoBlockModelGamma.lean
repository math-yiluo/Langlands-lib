import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationStatement
import Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionProof
import Langlands.Representation.RankinSelberg.TwoBlockModelGenericSocleOccurrenceProof
import Langlands.Representation.RankinSelberg.SubmodelGammaComparison
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Two-block gamma comparison through the actual generic model socles

Generic matrix functional-equation existence remains an explicit premise.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- The rational expression respects the product data of the two-block matrix
functional equation. This is an identity of rational functions. -/
theorem rationalGammaExpression_prod_two
    (δ : ℂˣ) (P PD : Fin 2 → Polynomial ℂ) (c : Fin 2 → ℂˣ) (a : Fin 2 → ℤ) :
    rationalGammaExpression δ (∏ i, c i) (∑ i, a i) (∏ i, P i) (∏ i, PD i) =
      ∏ i, rationalGammaExpression δ (c i) (a i) (P i) (PD i) := by
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, rationalGammaExpression,
    coe_rationalEpsilonMonomial, Units.val_mul, map_mul, zpow_add₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero)]
  ring

/-- The complete symmetric gamma certificate is unchanged by putting the
trivial scalar test first, including the equal-rank case. -/
theorem isPadicSymmetricGammaFactor_rankOne_one_swap
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) σ)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν σ (rankOneCharacter 1) G ↔
      IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter 1) σ G := by
  let := F.canonicalTopologicalData.topology
  cases n with
  | zero =>
    simp only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true]
    exact isPadicPairGammaFactor_swap_equalRank F ψ ν σ (rankOneCharacter 1)
      hσ (rankOneCharacter_isOfWhittakerType p F ψ 1) G
  | succ n =>
    simp only [IsPadicSymmetricGammaFactor, Nat.zero_le,
      show ¬ n + 1 ≤ 0 by omega, ite_true, ite_false]

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance modelGammaValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance modelGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance modelGammaMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelGammaBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelGammaT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelGammaDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelGammaGLMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear r F.Carrier) := borel _
local instance modelGammaGLBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear r F.Carrier) := ⟨rfl⟩

local instance modelGammaCoefficientGroup {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- Restrict the smooth Schur character to the actual scalar matrices. -/
private theorem modelGamma_scalarQuasicharacter {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ha : IsAdmissible σ) (hi : σ.IsIrreducible) :
    ∃ ω : Quasicharacter F.Carrier,
      Classification.HasGLCentralCharacter F.Carrier (n + 1) σ ω.toMonoidHom := by
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter σ ha hi
  let ω : Quasicharacter F.Carrier :=
    ⟨χ.comp GeneralLinear.scalarToCenter,
      hlc.continuous.comp (GeneralLinear.scalarContinuous.continuous.subtype_mk _)⟩
  exact ⟨ω, fun x v => hact (GeneralLinear.scalarToCenter x) v⟩

/-- Full Whittaker type supplies a complete gamma certificate independently
of the matrix comparison. -/
private theorem modelGamma_exists
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ G, IsPadicSymmetricGammaFactor F ψ ν.val σ (rankOneCharacter 1) G := by
  let G := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val σ (rankOneCharacter 1)
    (whittakerTypeGammaConstructionInput p F ψ ν n 0 V ℂ σ (rankOneCharacter 1)
      hσ (rankOneCharacter_isOfWhittakerType p F ψ 1))
  exact ⟨G.val, G.property⟩

/-- Data on a nonzero full-type submodel determine the gamma certificate of
the possibly reducible original. -/
private theorem modelGamma_from_submodel_data
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (S : Subrepresentation (glModelRepresentation ψ n σ ℓ)) (hS : S ≠ ⊥)
    (hStype : IsOfWhittakerType (V := S.toSubmodule)
      n (standardCharacter ψ n) S.toRepresentation)
    (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν.val
      (V := S.toSubmodule) S.toRepresentation P PD c a) :
    IsPadicSymmetricGammaFactor F ψ ν.val σ (rankOneCharacter 1)
      (rationalGammaExpression (LocalFactor.residueReflection F) c a P PD) := by
  let q : (⊤ : Subrepresentation S.toRepresentation).toRepresentation.IntertwiningMap
      S.toRepresentation :=
    { toLinearMap := (⊤ : Subrepresentation S.toRepresentation).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact gamma_of_submodel_ambient_matrix F ψ ν.val ν.property σ ℓ hℓ S hS hStype
    S.toRepresentation hStype.1.1 ⊤ q (fun v => ⟨⟨v, trivial⟩, rfl⟩)
    P PD c a hdata (modelGamma_exists F ψ ν σ hσ)

end Padic

/-- Internal conditional gamma reduction. Generic matrix-data existence on
irreducible field-universe carriers is the remaining analytic premise. -/
def TwoBlockGammaRankOneFromGenericMatrixStatement : Prop :=
  GodementJacquet.GenericMatrixFunctionalEquationStatement.{uF,uF} →
    TwoBlockGammaRankOneStatement.{uF,uV,uW}

set_option maxHeartbeats 800000 in
/-- The unchanged rank-one gamma target follows from full matrix data
existence on irreducible generic models. The analytic premise is explicit. -/
theorem twoBlockGammaRankOne_of_generic_matrix
    (hG : GodementJacquet.GenericMatrixFunctionalEquationStatement.{uF,uF}) :
    TwoBlockGammaRankOneStatement.{uF,uV,uW} := by
  apply twoBlockGammaRankOne_of_trivial_test
  intro p hp F ψ ν t m h W hadd hmod σ hσ
  classical
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  let : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : ∀ r : ℕ, MeasurableSpace (Langlands.GeneralLinear r F.Carrier) :=
    fun _ => borel _
  let : ∀ r : ℕ, BorelSpace (Langlands.GeneralLinear r F.Carrier) :=
    fun _ => ⟨rfl⟩
  choose ℓ hℓ using fun i => (hσ i).exists_ne_zero
  let : ∀ i, AddCommGroup (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
  choose Si hSi using fun i =>
    modelGenericSocle p hp F ψ (m i) (W i) (σ i) (hσ i) (ℓ i) (hℓ i)
  let R (i : Fin 2) : Type uF := (Si i).toSubmodule
  let : ∀ i, AddCommGroup (R i) := fun i => (Si i).toSubmodule.addCommGroup
  let : ∀ i, Module ℂ (R i) := fun i => inferInstance
  let τ (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (m i + 1) F.Carrier) (R i) := (Si i).toRepresentation
  have hτ (i : Fin 2) : IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) :=
    (hSi i).2.2.2
  choose P PD c a hdata using fun i =>
    hG p F ψ ν.val ν.property (m i) (R i) (τ i) (hτ i) (hSi i).2.1
  choose ω hω using fun i =>
    modelGamma_scalarQuasicharacter F (τ i) (hτ i).1 (hSi i).2.1
  let I := F.canonicalNormalizedProductInduced (succBlockShape m h) σ
  have hI : IsOfWhittakerType t (standardCharacter ψ t) I :=
    normalizedProductWhittakerType p F ψ t 2 m h σ hσ
  obtain ⟨ℓI, hℓI⟩ := hI.exists_ne_zero
  let : AddCommGroup (glCoefficientModel ψ t I ℓI).toSubmodule :=
    (glCoefficientModel ψ t I ℓI).toSubmodule.addCommGroup
  obtain ⟨S, hS⟩ := modelGenericSocle p hp F ψ t _ I hI ℓI hℓI
  let J := F.canonicalNormalizedProductInduced (succBlockShape m h) τ
  have hJ : IsSmooth J :=
    F.canonicalTopologicalData.isSmooth_normalizedProductInduced
      (succBlockShape m h) τ
  have hJdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData
      F ψ ν.val J (∏ i, P i) (∏ i, PD i) (∏ i, c i) (∑ i, a i) :=
    GodementJacquet.twoBlockMatrixFunctionalEquationInduction p F t m h R τ
      (fun i => (hτ i).1.1) (fun i => (hτ i).1) ψ ν.val ν.property ω hω P PD c a hdata
  obtain ⟨A, q, hq⟩ := twoBlockModelGenericSocleOccurrence p F ψ t m h W σ hσ
    ℓ hℓ ℓI hℓI Si S hSi hS
  have hIgamma := gamma_of_submodel_ambient_matrix F ψ ν.val ν.property I ℓI hℓI
    S hS.1 hS.2.2.2 J hJ A q hq (∏ i, P i) (∏ i, PD i)
    (∏ i, c i) (∑ i, a i) hJdata (modelGamma_exists F ψ ν I hI)
  let G (i : Fin 2) :=
    rationalGammaExpression (LocalFactor.residueReflection F) (c i) (a i) (P i) (PD i)
  refine ⟨G, fun i => ?_, ?_⟩
  · apply (isPadicSymmetricGammaFactor_rankOne_one_swap F ψ ν.val (σ i) (hσ i) (G i)).1
    exact modelGamma_from_submodel_data F ψ ν (σ i) (hσ i) (ℓ i) (hℓ i)
      (Si i) (hSi i).1 (hτ i) (P i) (PD i) (c i) (a i) (hdata i)
  · apply (isPadicSymmetricGammaFactor_rankOne_one_swap F ψ ν.val I hI (∏ i, G i)).1
    simpa only [rationalGammaExpression_prod_two] using hIgamma

end Langlands.RankinSelberg
