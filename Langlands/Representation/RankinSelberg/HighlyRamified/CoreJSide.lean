import Langlands.Representation.RankinSelberg.HighlyRamified.CoreAnalytic
import Langlands.Representation.RankinSelberg.HighlyRamified.DualReduction
import Langlands.Representation.RankinSelberg.HighlyRamified.DualJValue
import Langlands.Representation.RankinSelberg.HighlyRamified.DualEquivariance

/-!
# The value of the dual integral of a candidate test function

Jacquet and Shalika 1985, §4.4 (printed pages 328–330: (4.4.5)–(4.4.12), the relation
`J_i = c W_(i,0)(e)` on page 329 and `J₁ = J₂ ≠ 0` on page 330), the evaluation of `J`: the dual
corank-one integral of the candidate test function `χ(det y) Σ_z Φ(z) W(y w n(z))` against
`f̃'` reduces (`dual_integral_reduction`, `dual_inner_integral`) to the pairing of
`Ξ(A) = W(M(diag(A,1)))` with a function `F_n` built from the restriction
`F_A(A) = U(diag(A,1)) |det A|^(-1/2)` of the twisted smeared function `U`. If the weighted
`K⁰(f)`-average of `F_A` is `c₀` times the target, `dual_pairing_of_average_eq_target`
evaluates the pairing to `χ(det w) c₀ W(1)`. The positive constant `C'` of the reduction
depends only on the rank and the Haar measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance coreJFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance coreJValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance coreJLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance coreJFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance coreJFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance coreJGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance coreJGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreJUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance coreJUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreJQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance coreJQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩
local instance (priority := high) coreJLowerMeasurable : MeasurableSpace
    (lowerTriangularSubgroup (0 + 1) F.Carrier) := borel _
local instance (priority := high) coreJLowerBorel : BorelSpace
    (lowerTriangularSubgroup (0 + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {m : ℕ} {ω : F.Carrierˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- The determinant factor `|det A|⁻¹ |det A|^s` of the reduced pairing. -/
def jFactor (s : ℂ) (A : Langlands.GeneralLinear (m + 1) F.Carrier) : ℂ :=
  ((lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1
    (Quotient.mk _ A)).toReal : ℂ) * determinantWeight abv A s

theorem jFactor_unipotent (s : ℂ) (u : upperUnipotent (m + 1) F.Carrier)
    (A : Langlands.GeneralLinear (m + 1) F.Carrier) :
    jFactor F s (u.val * A) = jFactor F s A := by
  unfold jFactor
  rw [determinantWeight_unipotent_mul, lowerBlockQuotientDensity_mk,
    lowerBlockQuotientDensity_mk, Units.val_mul, Matrix.det_mul,
    show Matrix.det u.val.val = 1 from by
      have := determinant_unipotent_mul (F := F.Carrier) u 1
      simp at this ⊢, one_mul]

theorem jFactor_mul_integral (s : ℂ) (A k : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hk : k ∈ Conductor.levelOpenSubgroup F.Carrier m 0) :
    jFactor F s (A * k) = jFactor F s A := by
  have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer m := by
    rw [← Conductor.levelSubgroup_zero]; exact hk
  have h1 := normalizedAbs_det_of_mem_integralSubgroup F.canonicalTopologicalData hk'
  unfold jFactor
  rw [determinantWeight_mul_integral F A k hk, lowerBlockQuotientDensity_mk,
    lowerBlockQuotientDensity_mk, Units.val_mul, Matrix.det_mul,
    F.canonicalTopologicalData.normalizedAbs_mul, h1, mul_one]

/-- The factor is `1` where `ord det = 0`. -/
theorem jFactor_of_ord_zero (s : ℂ) {A : Langlands.GeneralLinear (m + 1) F.Carrier}
    (hA : F.canonicalTopologicalData.ord (determinant A : F.Carrier) = 0) :
    jFactor F s A = 1 := by
  have habs : F.canonicalTopologicalData.normalizedAbs (Matrix.det A.val) = 1 := by
    have := F.canonicalTopologicalData.normalizedAbs_of_ne_zero (determinant A).ne_zero
    change F.canonicalTopologicalData.normalizedAbs (determinant A : F.Carrier) = 1
    rw [this, hA]
    simp
  unfold jFactor determinantWeight
  rw [lowerBlockQuotientDensity_mk, normalizedAbsoluteValue_apply, habs]
  simp [_root_.zpow_neg_one]

include hf in
/-- `Ξ(A) = W(M(diag(A,1)))` is right invariant under the principal congruence subgroup of
level `f`. -/
theorem whittaker_dualConj_principal (hω : TrivialOnPrincipalUnits ω f)
    (W : Langlands.GeneralLinear (m + 1 + 2) F.Carrier → ℂ)
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 1 + 1) f → W (g * k) = W g)
    (hZ : ∀ (z : F.Carrierˣ) g, W (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2)) z * g) =
      (ω z : ℂ) * W g)
    (A l : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hl : l ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f) :
    W (dualConj (rankInclusion 1 (A * l))) = W (dualConj (rankInclusion 1 A)) := by
  have hlK : InFirstColumn f l :=
    principalCongruenceSubgroup_le_firstColumnCongruence _ m _ hl
  rw [map_mul, map_mul, whittaker_dualConj_firstColumn hf ω W hK hZ hlK]
  have h1 : ω (Units.mk0 (l 0 0) (firstColumn_entry_isUnit hf hlK).1) = 1 := by
    apply hω
    obtain ⟨y, hy, hye⟩ := firstEntry_mul_principal (k := 1) (one_mem _) hl
    refine ⟨y, hy, ?_⟩
    simpa using hye
  rw [h1]
  simp

/-- The dual corank-one integral of the candidate test function, evaluated: if the weighted
`K⁰(f)`-average of the restriction `F_A` of `U` is `c₀` times the target, and `U` is related
to the smeared dual function by `∫ S₂(rev x) f̃([[A,0],[x,1]]) dx = χ(det A) U(diag(A,1))`,
then the dual integral is `C' χ(det w) c₀ W(1)`, where `C' > 0` depends only on the rank and
the Haar measure. -/
theorem dual_integral_value (ηH : AdditiveHaarMeasure F.Carrier) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (_hψ : HasIntegerConductorAt F ψ) (χ : F.Carrierˣ →* ℂˣ)
      (hω : TrivialOnPrincipalUnits ω f)
      (W : WhittakerFunctions ψ (m + 2))
      (_hK : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 2) f → W.val (g * k) = W.val g)
      (_hZ : ∀ (z : F.Carrierˣ) g, W.val (Matrix.GeneralLinearGroup.scalar (Fin (m + 3)) z * g) =
        (ω z : ℂ) * W.val g)
      (T : Finset (Fin (m + 2) → F.Carrier))
      (Φ : (Fin (m + 2) → F.Carrier) → ℂ) (Fc : WhittakerFunctions ψ (m + 2))
      (_hFc : Fc.val = candidateTest ψ χ W T Φ)
      (S1 : F.Carrier → ℂ) (S2 : (Fin (m + 1) → F.Carrier) → ℂ) (η : F.Carrier → ℂ)
      (f' : InverseWhittakerFunctions ψ (m + 1))
      (_hfac : ∀ ξ : Fin (m + 2) → F.Carrier,
        (∀ k, ξ k ∈ (ValuativeRel.valuation F.Carrier).integer) →
        finiteFourier ψ T Φ ξ = S1 (ξ 0) * S2 (fun k => ξ k.succ))
      (_hS1 : ∀ c, S1 c ≠ 0 → c ∈ (ValuativeRel.valuation F.Carrier).integer ∧ c ≠ 0 ∧
        c⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer)
      (_hS2 : ∀ v, S2 v ≠ 0 → ∀ k, ∃ y : (ValuativeRel.valuation F.Carrier).integer,
        y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F.Carrier).integer ^ f ∧
          (y : F.Carrier) = v k)
      (_hη : ∀ (y : GeneralLinear (m + 1 + 1) F.Carrier)
        (c : lowerTriangularSubgroup 1 F.Carrier),
        c.val 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer →
        (c.val 0 0)⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer →
          (secondDualFunction ψ (m + 1) f').val
              (y * (lowerBlockPair 1 0 c : GeneralLinear (m + 1 + 1) F.Carrier)) =
            η (c.val 0 0) * (secondDualFunction ψ (m + 1) f').val y)
      (_hκ : ∀ c, lastWeight F χ S1 η c =
        ((unitLowerSubgroup F : Set (lowerTriangularSubgroup (0 + 1) F.Carrier))).indicator 1 c)
      (U : WhittakerFunctions ψ (m + 1))
      (_hU : ∀ A : Langlands.GeneralLinear (m + 1) F.Carrier,
        ∫ x, S2 (fun k => x 0 k.rev) * (secondDualFunction ψ (m + 1) f').val
          (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F.Carrier)
          ∂rectangularMeasure ηH 1 (m + 1) =
        (χ (determinant A) : ℂ) * U.val (rankInclusion 1 A))
      (LU : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
      (hUL : ∀ g l, l ∈ LU → U.val (g * l) = U.val g)
      (c₀ : ℂ)
      (_havg : ∀ g, rightAverage (generalLinearHaar F.Carrier m) (corankRestriction F ψ U)
        (LU.comap (rankInclusion 1) (rankInclusionContinuous 1).continuous ⊓
          Conductor.levelOpenSubgroup F.Carrier m 0)
        (corankRestriction_mul F ψ U LU hUL) (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g =
          c₀ * firstColumnTarget ω hf (standardCharacter ψ m) g)
      (s : ℂ),
      Measurable (corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s) →
      Integrable (corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s) (unipotentQuotientHaar F.Carrier (m + 1)) →
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier (m + 1))
          (firstDualFunction ψ (m + 2) Fc) (secondDualFunction ψ (m + 1) f') s =
        (C' : ℂ) * ((χ (determinant (weylLong (m + 3) F.Carrier)) : ℂ) * c₀ * W.val 1) := by
  obtain ⟨C', hC', hred⟩ := dual_integral_reduction F (m := m) ηH
  refine ⟨C', hC', ?_⟩
  intro ψ hψ χ hω W hK hZ T Φ Fc hFc S1 S2 η f' hfac hS1 hS2 hη hκ U hU LU hUL c₀ havg s
    hmeas hint
  obtain ⟨hint2, heq⟩ := hred ψ χ W T Φ Fc hFc S1 S2 η f' hψ.nontrivial hfac hS1 hS2 hK hη hκ s
    hmeas hint
  rw [heq]
  congr 1
  set wχ : ℂ := (χ (determinant (weylLong (m + 3) F.Carrier)) : ℂ) with hwχ
  set Ξ : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ :=
    fun A => W.val (dualConj (rankInclusion 1 A)) with hΞ
  set LA := LU.comap (rankInclusion 1) (rankInclusionContinuous 1).continuous ⊓
    Conductor.levelOpenSubgroup F.Carrier m 0 with hLA
  set Fn : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ :=
    fun A => wχ * jFactor F s A * corankRestriction F ψ U A with hFn
  have hκ1 : lastWeight F χ S1 η 1 = 1 := by
    rw [hκ 1, Set.indicator_of_mem (show (1 : lowerTriangularSubgroup (0 + 1) F.Carrier) ∈
      ((unitLowerSubgroup F : Set (lowerTriangularSubgroup (0 + 1) F.Carrier))) from
        one_mem (unitLowerSubgroup F))]
    rfl
  -- the inner integrals as the pairing integrand
  have hpt : ∀ q : LeftQuotient (upperUnipotent (m + 1) F.Carrier),
      ((lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1 q).toReal : ℂ) *
        ∫ x, corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
          (secondDualFunction ψ (m + 1) f') s (lowerBlockQuotientChart (q, x, 1))
          ∂rectangularMeasure ηH 1 (m + 1) = Ξ q.out * Fn q.out := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rw [dual_inner_integral F ηH ψ χ W T Φ Fc hFc S1 S2 η f' hψ.nontrivial hfac hS1 hS2 hK hη hκ1
      s q.out, hU q.out]
    have hdet0 : (abv (Matrix.det q.out.val) : ℂ) ≠ 0 := by
      have hpos := AbsoluteValue.pos abv (determinant q.out).ne_zero
      exact_mod_cast hpos.ne'
    have hsplit : determinantWeight abv q.out (s - 1 / 2) =
        determinantWeight abv q.out s * determinantWeight abv q.out (0 - 1 / 2) := by
      unfold determinantWeight
      rw [← Complex.cpow_add _ _ hdet0]
      ring_nf
    have hχ0 : (χ (determinant q.out) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [hFn, hΞ, jFactor, corankRestriction, hsplit]
    field_simp
    ring
  have hint3 : Integrable (fun q : LeftQuotient (upperUnipotent (m + 1) F.Carrier) =>
      Ξ q.out * Fn q.out) (unipotentQuotientHaar F.Carrier m) := by
    refine hint2.congr (Filter.Eventually.of_forall fun q => ?_)
    exact hpt q
  rw [show (fun q => ((lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1 q).toReal :
      ℂ) * ∫ x, corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s (lowerBlockQuotientChart (q, x, 1))
        ∂rectangularMeasure ηH 1 (m + 1)) = fun q => Ξ q.out * Fn q.out from funext hpt]
  -- the pairing
  have hFnL : ∀ g l, l ∈ LA → Fn (g * l) = Fn g := by
    intro g l hl
    simp only [hFn]
    rw [jFactor_mul_integral F s g l hl.2, corankRestriction_mul F ψ U LU hUL g l hl]
  have hψN : ∀ n : upperUnipotent (m + 1) F.Carrier,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) →
        standardCharacter ψ m n = 1 :=
    fun n hn => standardCharacter_eq_one_of_integral F ψ hψ n hn
  have hval := dual_pairing_of_average_eq_target F hf hω (standardCharacter ψ m) hψN Ξ Fn
    (Conductor.principalLevelOpenSubgroup F.Carrier m f) LA
    (fun g l hl => whittaker_dualConj_principal F hf hω W.val hK hZ g l hl) hFnL
    (fun g k hk => by
      simp only [hΞ]
      rw [map_mul, map_mul]
      exact whittaker_dualConj_firstColumn hf ω W.val hK hZ hk _)
    (fun u g => whittaker_dualConj_unipotent F ψ W u g)
    (fun u g => by
      simp only [hFn]
      rw [jFactor_unipotent, corankRestriction_unipotent]
      ring)
    hint3 (wχ * c₀)
    (fun g => by
      rw [rightAverage_apply]
      have hg := havg g
      rw [rightAverage_apply] at hg
      have hfac' : ∀ k, firstColumnWeight ω hf k * Fn (g * k) =
          (wχ * jFactor F s g) * (firstColumnWeight ω hf k * corankRestriction F ψ U (g * k)) := by
        intro k
        by_cases hk : InFirstColumn f k
        · simp only [hFn]
          have hk0 := firstColumnCongruence_le_integralSubgroup _ m _ hk
          rw [← Conductor.levelSubgroup_zero] at hk0
          rw [jFactor_mul_integral F s g k hk0]
          ring
        · rw [firstColumnWeight_of_not_mem ω hf hk]
          ring
      simp_rw [hfac']
      rw [integral_const_mul, hg]
      by_cases ht : firstColumnTarget ω hf (standardCharacter ψ m) g = 0
      · rw [ht]; ring
      · rw [jFactor_of_ord_zero F s (firstColumnTarget_ord_det F hf _ ht)]
        ring)
  rw [hval]
  have h1 : Ξ 1 = W.val 1 := by
    simp only [hΞ, map_one]
  rw [h1]

end Langlands.RankinSelberg.HighlyRamified
