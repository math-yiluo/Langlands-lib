import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLaurent
import Langlands.Representation.RankinSelberg.LaurentPoleResidue
import Langlands.Representation.RankinSelberg.PadicCovariantPairing

/-! # Equal-rank denominator roots give contragredient twists -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section Family

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- Evaluation at a nonzero point of the normalized denominator-cleared
continuation on the original vectors and the actual row test. -/
def equalRankVectorResidue (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (x : ℂˣ) :
    V →ₗ[ℂ] W →ₗ[ℂ] SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] ℂ :=
  clearedLaurentForm P (equalRankVectorContinuation hq hA)
    (equalRankVectorContinuation_clears hq hA hP) x

theorem equalRankVectorResidue_ne_zero (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (x : ℂˣ) : equalRankVectorResidue hq hA hP x ≠ 0 :=
  clearedLaurentForm_ne_zero hP _ _ (fun R hR =>
    (mem_equalRankRationalValues_iff_vector hq hA R).mp hR) x

variable [IsTopologicalRing F] [BorelSpace (LeftUnipotentQuotient n F)]

/-- Clearing and evaluating preserves the actual translation law without any
denominator guard on the original rational continuation. -/
theorem equalRankVectorResidue_translate (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (x : ℂˣ) (g : Langlands.GeneralLinear (n + 1) F) (m : ℤ)
    (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (v : V) (w : W) (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankVectorResidue hq hA hP x (π g v) (σ g w) (rowTranslate g Φ) =
      (x : ℂ) ^ m * equalRankVectorResidue hq hA hP x v w Φ := by
  let C := equalRankVectorContinuation hq hA
  let hc := equalRankVectorContinuation_clears hq hA hP
  let a := laurentLift P C hc v w Φ
  have ha : laurentToRatFunc a = algebraMap (Polynomial ℂ) RationalFunctions P * C v w Φ :=
    laurentLift_spec P C hc v w Φ
  have hat : laurentToRatFunc (LaurentPolynomial.T m * a) =
      algebraMap (Polynomial ℂ) RationalFunctions P *
        C (π g v) (σ g w) (rowTranslate g Φ) := by
    rw [map_mul, laurentToRatFunc_T, ha,
      show C (π g v) (σ g w) (rowTranslate g Φ) = RatFunc.X ^ m * C v w Φ from
        equalRankVectorContinuation_translate hq hA hμ g m hg v w Φ]
    ring
  change clearedLaurentForm P C hc x (π g v) (σ g w) (rowTranslate g Φ) =
    (x : ℂ) ^ m * clearedLaurentForm P C hc x v w Φ
  rw [clearedLaurentForm_eq P C hc x _ _ _ _ hat, map_mul, laurentEval_T,
    clearedLaurentForm_eq P C hc x v w Φ a ha]

end Family

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance residueFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance residueFieldValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance residueFieldLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance residueFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {ψ : UnitaryAdditiveCharacter F.Carrier}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

local instance residueQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel _
local instance residueQuotientBorel : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {μ : Measure (LeftUnipotentQuotient n F.Carrier)}

/-- A denominator root at `q^u` descends through evaluation of the row test at
zero to a nonzero bilinear form with covariance `|det|^u`. -/
theorem hasNonzeroPadicCovariantPairing_of_supercuspidal_root
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0)
    (hA : EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F.Carrier) g) μ μ)
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ') P)
    (u : ℂ) (hu : P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (-u)) = 0) :
    HasNonzeroPadicCovariantPairing F.canonicalTopologicalData π σ u := by
  let T := F.canonicalTopologicalData
  let x := spectralUnit (Nat.zero_lt_one.trans T.residueCardinality_gt_one) (-u)
  let C := equalRankVectorContinuation T.residueCardinality_gt_one hA
  let hc := equalRankVectorContinuation_clears T.residueCardinality_gt_one hA hP
  let B := clearedLaurentForm P C hc x
  have hvalues : ∀ R ∈ equalRankRationalValues T.residueCardinality ψ
      (normalizedAbsoluteValue T) μ π σ ℓ ℓ', ∃ v w Φ, C v w Φ = R :=
    fun R hR => (mem_equalRankRationalValues_iff_vector T.residueCardinality_gt_one hA R).mp hR
  have hreg : ∀ v w Φ, rowEvaluationAtZero Φ = 0 →
      ∃ a : LaurentCoefficients, laurentToRatFunc a = C v w Φ :=
    fun v w Φ hΦ => equalRankVectorContinuation_laurent_of_supercuspidalKirillov
      hK hπ hiπ hℓ hA v w Φ hΦ
  have hB := clearedLaurentForm_ne_zero hP C hc hvalues x
  have hvan := clearedLaurentForm_vanishes_on P C hc
    (LinearMap.ker rowEvaluationAtZero) hreg x hu
  have he : ∃ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier), rowEvaluationAtZero Φ ≠ 0 := by
    by_contra h
    push Not at h
    apply hB
    ext v w Φ
    exact congrArg (fun D => D v w ⟨Φ, h Φ⟩) hvan
  obtain ⟨Φ, hΦ⟩ := he
  let Φ₀ := (rowEvaluationAtZero Φ)⁻¹ • Φ
  have hΦ₀ : rowEvaluationAtZero Φ₀ = 1 := by
    dsimp only [Φ₀]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hΦ]
  have hinv : TrilinearReduction.Invariant π σ
      (fun g => (rowTranslate g).toLinearMap)
      (fun g => determinantWeight (normalizedAbsoluteValue T) g u) B := by
    intro g v w Ψ
    let m := -T.ord (Matrix.det g.val)
    have hg : normalizedAbsoluteValue T (Matrix.det g.val) = (T.residueCardinality : ℝ) ^ m := by
      rw [normalizedAbsoluteValue_apply,
        T.normalizedAbs_of_ne_zero (Matrix.isUnits_det_units g).ne_zero]
    have ht := equalRankVectorResidue_translate T.residueCardinality_gt_one hA hP hμ
      x g m hg v w Ψ
    have hw := determinantWeight_neg_eq_spectralPoint_zpow
      (Nat.zero_lt_one.trans T.residueCardinality_gt_one) (normalizedAbsoluteValue T)
      g m hg (-u)
    rw [neg_neg] at hw
    change B (π g v) (σ g w) (rowTranslate g Ψ) =
      determinantWeight (normalizedAbsoluteValue T) g u * B v w Ψ
    rw [hw]
    exact ht
  obtain ⟨β, hβ, _, hcov⟩ := exists_bilinear_of_clearedLaurent_root hP C hc hvalues
    rowEvaluationAtZero Φ₀ hΦ₀ hreg π σ
    (fun g => (rowTranslate g).toLinearMap)
    (fun g => determinantWeight (normalizedAbsoluteValue T) g u)
    (fun g Ψ => rowEvaluationAtZero_translate g Ψ) x hu hinv
  exact ⟨β, hβ, hcov⟩

/-- Each root gives the normalized inverse-power twist equivalence appearing
in the equal-rank supercuspidal L-factor statement. -/
theorem exists_contragredient_twist_of_supercuspidal_root
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0)
    (hσ : IsAdmissible σ) (hiσ : σ.IsIrreducible)
    (hA : EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F.Carrier) g) μ μ)
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ') P)
    (u : ℂ) (hu : P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (-u)) = 0) :
    ∃ χ : F.Carrierˣ →* ℂˣ,
      (∀ x : F.Carrierˣ,
        (χ x : ℂ) = ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ (-u)) ∧
      Nonempty ((Langlands.twist (χ.comp determinant) π).Equiv (smoothContragredient σ)) :=
  HasNonzeroPadicCovariantPairing.exists_contragredient_equiv
    F.canonicalTopologicalData π σ u hiπ hiσ hπ.1.1 hσ
    (hasNonzeroPadicCovariantPairing_of_supercuspidal_root
      hK hπ hiπ hℓ hA hμ hP u hu)

end Padic

end Langlands.RankinSelberg
