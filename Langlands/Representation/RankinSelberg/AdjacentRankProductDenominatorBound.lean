import Langlands.Representation.RankinSelberg.AdjacentRankMatrixWitnesses
import Langlands.Representation.GodementJacquet.ProductGenerators

/-! The product of the two certified ordinary polynomials bounds realized corank values. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance productBoundTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance productBoundValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance productBoundLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance productBoundFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance productBoundFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance productBoundFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance productBoundFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance productBoundGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance productBoundGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance productBoundUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance productBoundUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance productBoundQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance productBoundQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

local instance productBoundModelAddCommGroup
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) :
    AddCommGroup (glCoefficientModel ψ r σ ℓ).toSubmodule :=
  (glCoefficientModel ψ r σ ℓ).toSubmodule.addCommGroup

/-- Every rational continuation of a specified actual corank integral lies
in the Laurent span of the reciprocal of the proposed polynomial. -/
def AdjacentRankCorankDenominatorBound
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (P : Polynomial ℂ) : Prop :=
  ∀ R : RationalFunctions,
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s) R →
      R ∈ Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹}

/-- The actual matched finite product belongs to the reciprocal Laurent span
of the product of the supplied complete equal-rank and twisted rank-one
polynomial certificates. No factor-existence or image-equality claim is made. -/
theorem adjacentRankProductContinuation_denominatorBound
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r N : ℕ} [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r τ ℓ'))
    (M : Fin N → RationalFunctions) (c : ℂ)
    (hM : ∀ i, GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) Φ
      (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i))
    (hdata : AdjacentRankProductContinuationData F ψ ν W.val
      (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
      U W' Φ φ χ (fun i => (f i).val) M c)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ μ σ τ P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) μ
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter 1) P₁) :
    AdjacentRankCorankDenominatorBound F ψ ν U W' (P₀ * P₁) := by
  classical
  let τT := Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) τ
  let ℓT := determinantTwistFunctionalEquiv (ψ.scale (-1)) χ τ ℓ'
  have hτT : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τT :=
    (isOfWhittakerType_quasicharacter_twist_iff F.canonicalTopologicalData
      (ψ.scale (-1)) χ τ).mpr hτ
  have hℓT : ℓT.val ≠ 0 := hℓ'
  let hopen := quasicharacter_isOpen_ker F.canonicalTopologicalData χ
  let fT i := GodementJacquet.determinantTwistModelCoefficient
    (ψ.scale (-1)) χ hopen τ ℓ' (f i)
  have hgen₁ : GodementJacquet.Padic.IsMatrixNormalizedGenerator F
      (V := (glCoefficientModel (ψ.scale (-1)) r τT ℓT).toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r τT ℓT) P₁ :=
    GodementJacquet.Padic.isMatrixNormalizedGenerator_model_of_pair
    F (ψ.scale (-1)) τT μ hτT hP₁ ℓT hℓT
  have hPair₀ : IsPadicPairLPolynomial F ψ μ σ τ P₀ :=
    (isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp hP₀
  have hEq₀ : IsPairLPolynomial qF ψ abv ν μ σ τ P₀ := hPair₀.2 ν hν
  have hgen₀ : IsNormalizedGenerator (equalRankZetaValues qF ψ abv ν σ τ) P₀ :=
    (isPairLPolynomial_self (π := σ) (σ := τ)).mp hEq₀
  have hprod := GodementJacquet.normalizedGenerator_productRationalValues hgen₀ hgen₁
  obtain ⟨A, hA, ⟨a, ha⟩, -, huniq⟩ := hdata
  have hAmem (i : Fin N) : A i ∈ equalRankZetaValues qF ψ abv ν σ τ := by
    refine ⟨W.val, coefficientModel_subset_whittakerSet ℓ W.property,
      InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val, ?_, φ,
      ⟨a, fun s hs => (ha s hs).2.1 i⟩, hA i⟩
    exact coefficientModel_subset_inverseWhittakerSet
      (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')
      (scaledStandardCoefficientAsInverse F ψ τ ℓ' (B i)).property
  have hMmem (i : Fin N) : M i ∈ GodementJacquet.matrixRationalValues
      (V := (glCoefficientModel (ψ.scale (-1)) r τT ℓT).toSubmodule) qF abv
      (generalLinearHaar F.Carrier r)
      (glModelRepresentation (ψ.scale (-1)) r τT ℓT) :=
    ⟨Φ, fT i, hM i⟩
  have hsum : (∑ i, A i * M i) ∈ zetaSpan (GodementJacquet.productRationalValues
      (equalRankZetaValues qF ψ abv ν σ τ)
      (GodementJacquet.matrixRationalValues
        (V := (glCoefficientModel (ψ.scale (-1)) r τT ℓT).toSubmodule)
        qF abv (generalLinearHaar F.Carrier r)
        (glModelRepresentation (ψ.scale (-1)) r τT ℓT))) := by
    apply Submodule.sum_mem
    intro i _
    exact mem_zetaSpan (GodementJacquet.mem_productRationalValues.mpr
      ⟨A i, hAmem i, M i, hMmem i, rfl⟩)
  intro R hR
  rw [huniq R hR]
  exact hprod.2 ▸ GodementJacquet.const_mul_mem_zetaSpan c hsum

end Langlands.RankinSelberg.Padic
