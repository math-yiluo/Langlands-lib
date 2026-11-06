import Langlands.Representation.RankinSelberg.SupercuspidalRowIntegrals
import Langlands.Representation.RankinSelberg.TwistedCentralScalar
import Langlands.Representation.RankinSelberg.CompactLaurentEvaluation
import Langlands.Representation.RankinSelberg.NormalizedGeneratorRegularityProof
import Langlands.Representation.RankinSelberg.AnalyticBridge

/-! # A contragredient twist forces a root of the equal-rank denominator -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open RationalEvaluation

universe uF uV uW

section Regularity

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- Away from zero and the roots of the normalized denominator, every vector
continuation is regular. -/
theorem equalRankVectorContinuation_regularAt_of_eval_ne_zero
    (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    {x : ℂ} (hx : x ≠ 0) (hPx : P.eval x ≠ 0)
    (v : V) (w : W) (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    RegularAt (equalRankVectorContinuation hq hA v w Φ) x := by
  obtain ⟨a, ha⟩ := equalRankVectorContinuation_clears hq hA hP v w Φ
  have hpoly : RatFunc.eval (RingHom.id ℂ) x
      (algebraMap (Polynomial ℂ) RationalFunctions P) ≠ 0 := by
    simpa using hPx
  have hregular := (regularAt_laurentToRatFunc a hx).mul (RegularAt.inv hpoly)
  rw [ha, mul_right_comm,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hP.polynomial_ne_zero), one_mul] at hregular
  exact hregular

end Regularity

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance twistRootTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance twistRootValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance twistRootLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance twistRootT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

variable {n : ℕ}

local instance twistRootGLMeasurable :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance twistRootGLBorel :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance twistRootNMeasurable :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance twistRootNBorel :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance twistRootQMeasurable :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance twistRootQBorel :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {ψ : UnitaryAdditiveCharacter F.Carrier}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
  {μ : Measure (LeftUnipotentQuotient n F.Carrier)}

/-- Every actual normalized contragredient twist is a root parameter of `P`. -/
def HasNormalizedContragredientTwistRoots (P : Polynomial ℂ) : Prop :=
  ∀ u : ℂ,
    Nonempty ((Langlands.twist
      (F.canonicalTopologicalData.determinantComplexPower (n + 1) (-u)) π).Equiv
        (smoothContragredient σ)) →
    P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (-u)) = 0

set_option maxHeartbeats 800000 in
/-- The positive compact central shell excludes regularity at the twist point.
The analytic conclusion and normalized denominator refer to the fixed pair of
nonzero Whittaker functionals. -/
theorem supercuspidal_root_of_contragredient_twist
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hiσ : σ.IsIrreducible) (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (hA : EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ')
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ') P)
    (u : ℂ)
    (he : Nonempty ((Langlands.twist
      (F.canonicalTopologicalData.determinantComplexPower (n + 1) (-u)) π).Equiv
        (smoothContragredient σ))) :
    P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (-u)) = 0 := by
  classical
  let T := F.canonicalTopologicalData
  let x := spectralPoint T.residueCardinality (-u)
  have hx : x ≠ 0 := by
    exact (spectralUnit (Nat.zero_lt_one.trans T.residueCardinality_gt_one) (-u)).ne_zero
  by_contra hPx
  let : μ.Regular := hμ.regular
  have hc := hasCompactSupercuspidalRowIntegrands_of_kirillov hK hπ hiπ hℓ
  have hcoeff := hasPadicTwistedPositiveCoefficients_of_contragredient_twist
    T π σ ψ u hiπ hπ hσ.1 he ℓ hℓ
  obtain ⟨Φ, _, hΨ0, m, _, v, w, hconv, hpos⟩ :=
    hcoeff.exists_positive_central_shell_integral hℓ hc hμ.isOpenPosMeasure
      (inferInstance : IsFiniteMeasureOnCompacts μ) hπ.1.1 hσ.1.1
  let z := centralSpectralElement T (n + 1)
  let Ψ := Φ - rowTranslate z Φ
  obtain ⟨d, hmd⟩ := hσ.eq_smul hℓ' m
  have hcoefficient : coefficientMap σ m w = coefficientMap σ ℓ' (d • w) := by
    rw [hmd]
    apply Subtype.ext
    funext g
    change (d • ℓ').val (σ g w) = ℓ'.val (σ g (d • w))
    simp only [Submodule.coe_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hcoefficient] at hconv hpos
  let w' := d • w
  let C := equalRankVectorContinuation T.residueCardinality_gt_one hA
  have hspec : HasRationalContinuation T.residueCardinality
      (equalRankIntegral ψ (normalizedAbsoluteValue T) μ
        (coefficientMap π ℓ v) (coefficientMap σ ℓ' w') Ψ) (C v w' Ψ) := by
    exact equalRankContinuationFamily_spec T.residueCardinality_gt_one hA
      (modelMap π ℓ v) (modelMap σ ℓ' w') Ψ
  have hE := equalRankContinuation_regular_and_eval_of_hasCompactSupport T μ ψ
    (coefficientMap π ℓ v) (coefficientMap σ ℓ' w') Ψ
    (hc v (coefficientMap σ ℓ' w') Ψ hΨ0 0)
    (hA.1 (modelMap π ℓ v) (modelMap σ ℓ' w') Ψ)
    (C v w' Ψ)
    hspec
    (-u) hconv
  have hD := equalRankVectorContinuation_regularAt_of_eval_ne_zero
    T.residueCardinality_gt_one hA hP hx hPx v w' Φ
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter π hπ.1 hiπ
  obtain ⟨η, ⟨_, hη⟩, _⟩ := admissibleSchur_centralCharacter σ hσ.1 hiσ
  let zc : Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    ⟨z, centralSpectralElement_mem_center T (n + 1)⟩
  let a : ℂ := χ zc
  let b : ℂ := η zc
  let c := a * b
  have hcne : c ≠ 0 := mul_ne_zero (χ zc).ne_zero (η zc).ne_zero
  have hcentral := hasDeterminantCentralScalarIdentity_of_contragredient_twist
    T π σ u hiπ he
  have hcx := hcentral.spectralPoint_identity T π σ a b (hχ zc) (hη zc)
  have hneg : spectralPoint T.residueCardinality (-u) =
      (spectralPoint T.residueCardinality u)⁻¹ := by
    rw [spectralPoint, spectralPoint, neg_neg, Complex.cpow_neg, inv_inv]
  have hcroot : c = x ^ (n + 1) := by
    change c = spectralPoint T.residueCardinality (-u) ^ (n + 1)
    rw [hneg, inv_pow]
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hcx)
  have hshift : c • C v w' (rowTranslate z Φ) =
      (RatFunc.X : RationalFunctions) ^ (n + 1) * C v w' Φ := by
    have ht := equalRankVectorContinuation_translate T.residueCardinality_gt_one hA
      hμ.right_invariant z (n + 1 : ℕ)
      (by simpa only [zpow_natCast] using centralSpectralElement_det_abs T (n + 1))
      v w' Φ
    rw [hχ zc, hη zc] at ht
    simpa only [map_smul, LinearMap.smul_apply, RingHom.id_apply,
      smul_smul, zpow_natCast, mul_comm (η zc : ℂ) (χ zc : ℂ)] using ht
  have hdiff : RatFunc.C c * C v w' Ψ =
      algebraMap (Polynomial ℂ) RationalFunctions
        (Polynomial.C c - Polynomial.X ^ (n + 1)) * C v w' Φ := by
    rw [RatFunc.smul_eq_C_mul] at hshift
    change RatFunc.C c * C v w' (Φ - rowTranslate z Φ) = _
    rw [map_sub, mul_sub, hshift, map_sub, map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    ring
  have hCreg : RegularAt (RatFunc.C c : RationalFunctions) x := by
    simpa using (RegularAt.polynomial (z := x) (Polynomial.C c))
  have heval := congrArg (RatFunc.eval (RingHom.id ℂ) x) hdiff
  rw [RationalEvaluation.eval_mul hCreg hE.1,
    RationalEvaluation.eval_mul (RegularAt.polynomial _) hD] at heval
  have hzero : RatFunc.eval (RingHom.id ℂ) x (C v w' Ψ) = 0 := by
    have hz : c * RatFunc.eval (RingHom.id ℂ) x (C v w' Ψ) = 0 := by
      rw [RatFunc.eval_C, RingHom.id_apply, RatFunc.eval_algebraMap] at heval
      simpa only [Algebra.algebraMap_self_apply, Polynomial.eval₂_id,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, ← hcroot, sub_self, zero_mul] using heval
    exact (mul_eq_zero.mp hz).resolve_left hcne
  rw [hE.2] at hzero
  rw [hzero, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

end Padic

end Langlands.RankinSelberg
