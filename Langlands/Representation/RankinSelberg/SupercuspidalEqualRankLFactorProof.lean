import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankResidue
import Langlands.Representation.RankinSelberg.SupercuspidalTwistRoot
import Langlands.Representation.RankinSelberg.NormalizedRootProduct
import Langlands.Representation.RankinSelberg.SupercuspidalTwistParameters
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof

/-! # Equal-rank supercuspidal L-polynomial -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

private theorem exists_spectralPoint_of_ne_zero {q : ℕ} (hq : 1 < q)
    {a : ℂ} (ha : a ≠ 0) : ∃ u : ℂ, spectralPoint q u = a := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : (Real.log (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hqR).ne'
  have hqC : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_one.trans hq).ne'
  refine ⟨-Complex.log a / (Real.log (q : ℝ) : ℂ), ?_⟩
  rw [spectralPoint, Complex.cpow_def_of_ne_zero hqC, ← Complex.natCast_log]
  have he : (Real.log (q : ℝ) : ℂ) *
      -(-Complex.log a / (Real.log (q : ℝ) : ℂ)) = Complex.log a := by
    field_simp
  rw [he, Complex.exp_log ha]

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance assemblyFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance assemblyFieldValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance assemblyFieldLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance assemblyFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance assemblyFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance assemblyFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {ψ : UnitaryAdditiveCharacter F.Carrier}
  {ν : AdditiveHaarMeasure F.Carrier}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

local instance assemblyQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel _
local instance assemblyQuotientBorel : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local instance assemblyGLTopologicalGroup :
    IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)

local instance assemblyGLMeasurable :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance assemblyGLBorel :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance assemblyUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance assemblyUnipotentBorel :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable {μ : Measure (LeftUnipotentQuotient n F.Carrier)}

private theorem equalRank_product_of_converse
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0)
    (hσ : IsAdmissible σ) (hiσ : σ.IsIrreducible)
    (hA : EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F.Carrier) g) μ μ)
    {P : ℂ[X]}
    (hP : IsNormalizedGenerator (equalRankRationalValues
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ') P)
    (hPadic : IsPadicPairLPolynomial F ψ ν π σ P)
    (hC : ∀ u : ℂ,
      Nonempty ((Langlands.twist
        (F.canonicalTopologicalData.determinantComplexPower (n + 1) (-u)) π).Equiv
        (smoothContragredient σ)) →
      P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (-u)) = 0) :
    ∃ A : Finset ℂ,
      (∀ a : ℂ, a ∈ A ↔ IsContragredientTwistParameter F π σ a) ∧
      IsPadicPairLPolynomial F ψ ν π σ (∏ a ∈ A, (1 - C a * X)) := by
  classical
  let T := F.canonicalTopologicalData
  obtain ⟨c, hc, hdiv, hsep, hsq⟩ :=
    equalRank_normalizedGenerator_bound_of_supercuspidalKirillov
      supercuspidalKirillov hπ hiπ hℓ hσ hiσ hA hμ hP
  refine ⟨reciprocalRootParameters P, ?_, ?_⟩
  · intro a
    rw [mem_reciprocalRootParameters hP.1 a]
    constructor
    · rintro ⟨ha, hroot⟩
      obtain ⟨u, hu⟩ := exists_spectralPoint_of_ne_zero T.residueCardinality_gt_one ha
      have hpoint : spectralPoint T.residueCardinality (-u) = a⁻¹ := by
        rw [← hu]
        simp only [spectralPoint, neg_neg, Complex.cpow_neg, inv_inv]
      obtain ⟨χ, hχ, he⟩ := exists_contragredient_twist_of_supercuspidal_root
        supercuspidalKirillov hπ hiπ hℓ hσ hiσ hA hμ hP u (hpoint ▸ hroot)
      exact ⟨u, hu.symm, χ, hχ, he⟩
    · intro ha
      refine ⟨ha.ne_zero, ?_⟩
      obtain ⟨u, hu, χ, hχ, he⟩ := ha
      have hchar : χ.comp determinant = T.determinantComplexPower (n + 1) (-u) := by
        apply MonoidHom.ext
        intro g
        apply Units.ext
        change (χ (determinant g) : ℂ) = _
        rw [hχ, T.determinantComplexPower_apply]
        rfl
      rw [hchar] at he
      have hroot := hC u he
      simpa only [hu, spectralPoint, neg_neg, Complex.cpow_neg, inv_inv] using hroot
  · rw [← eq_prod_reciprocalRootParameters hP.1 hsep]
    exact hPadic

private theorem equalRank_intrinsic_setup
    (νs : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) (P : ℂ[X]),
      ℓ.val ≠ 0 ∧ ℓ'.val ≠ 0 ∧
      EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (unipotentQuotientHaar F.Carrier n) π σ ℓ ℓ' ∧
      IsNormalizedGenerator (equalRankRationalValues
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (unipotentQuotientHaar F.Carrier n) π σ ℓ ℓ') P ∧
      IsPadicPairLPolynomial F ψ νs.val π σ P := by
  let T := F.canonicalTopologicalData
  obtain ⟨ℓ, hℓ⟩ := Whittaker.SupercuspidalKirillovProof.exists_functional T ψ n
    (SmoothRep.of π hπ.1.1) hiπ hπ
  have hπtype : IsOfWhittakerType n (standardCharacter ψ n) π :=
    isOfWhittakerType_of_isGeneric F ⟨hiπ, hπ.1, ℓ, hℓ⟩
  have hσinverse := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  obtain ⟨ℓ', hℓ'⟩ := hσinverse.exists_ne_zero
  let := unipotentHaar_isMulRightInvariant F.Carrier n
  let μ := unipotentQuotientHaar F.Carrier n
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier n
  have hA := equalRankAnalytic.{uF,uV,uW} F T n ψ μ hμ
    V W π σ hπtype hσinverse ℓ ℓ' hℓ hℓ'
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists.{uF,uV,uW}
    p F ψ νs n n V W π σ hπtype hσ
  have hPadic : IsPadicPairLPolynomial F ψ νs.val π σ P := by
    simpa only [IsPadicSymmetricLPolynomial, ite_eq_left (Nat.le_refl n)] using hP
  have hPequal := isPairLPolynomial_self.mp (hPadic.2 μ hμ)
  exact ⟨ℓ, ℓ', P, hℓ, hℓ', hA,
    (hA.isEqualRankLPolynomial_iff hπtype hσinverse hℓ hℓ' P).mp hPequal, hPadic⟩

private theorem equalRank_conclusion_of_converse
    (νs : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hiσ : σ.IsIrreducible)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (hC : ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) (P : ℂ[X]),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (unipotentQuotientHaar F.Carrier n) π σ ℓ ℓ' →
      IsNormalizedGenerator (equalRankRationalValues
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (unipotentQuotientHaar F.Carrier n) π σ ℓ ℓ') P →
      ∀ u : ℂ, Nonempty ((Langlands.twist
        (F.canonicalTopologicalData.determinantComplexPower (n + 1) (-u)) π).Equiv
        (smoothContragredient σ)) →
        P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (-u)) = 0) :
    ∃ A : Finset ℂ,
      (∀ a : ℂ, a ∈ A ↔ IsContragredientTwistParameter F π σ a) ∧
      IsPadicPairLPolynomial F ψ νs.val π σ (∏ a ∈ A, (1 - C a * X)) := by
  obtain ⟨ℓ, ℓ', P, hℓ, hℓ', hA, hP, hPadic⟩ := equalRank_intrinsic_setup νs hπ hiπ hσ
  exact equalRank_product_of_converse hπ hiπ hℓ hσ.1 hiσ hA
    (unipotentQuotientHaar_isCompatible F.Carrier n).right_invariant hP hPadic
    (hC ℓ ℓ' P hℓ hℓ' hA hP)

end Padic

/-- JPSS (8.1)(ii), with the contragredient convention of the statement. -/
theorem supercuspidalEqualRankLFactor :
    SupercuspidalEqualRankLFactorStatement.{uF,uV,uW} := by
  intro p hp F ψ ν r V _ _ W _ _ π σ hiπ hπ hiσ hσ
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  let : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
  let : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
  let : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : IsTopologicalGroup (Langlands.GeneralLinear (r + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
  let : MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
  let : BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
  let := unipotentHaar_isMulRightInvariant F.Carrier r
  apply equalRank_conclusion_of_converse ν hπ hiπ hiσ hσ
  intro ℓ ℓ' P hℓ hℓ' hA hP u he
  exact supercuspidal_root_of_contragredient_twist
    supercuspidalKirillov hπ hiπ
    ((isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ) hiσ hℓ hℓ'
    (unipotentQuotientHaar_isCompatible F.Carrier r) hA hP u he

end Langlands.RankinSelberg
