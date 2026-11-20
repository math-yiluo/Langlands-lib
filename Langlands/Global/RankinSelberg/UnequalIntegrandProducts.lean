import Langlands.Global.RankinSelberg.EqualIntegrandProducts
import Langlands.Global.RankinSelberg.UnfoldingOrdinary
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-! # Ordinary unequal-rank integrand products from paired Whittaker products -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uK

open NumberField MeasureTheory
open scoped Classical

namespace Langlands.Global.RankinSelbergGlobal.UnequalIntegrandProducts

open RankinSelberg EqualIntegrandProducts

section Local

variable {K : Type uK} [Field K] {r t : ℕ}

private theorem padGL_eq_appendIdentity (k : ℕ) (h : t < t + (0 + k + 1))
    (g : Langlands.GeneralLinear (t + 1) K) :
    padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g = appendIdentity t (0 + k + 1) g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Unfolding.padGL_apply, appendIdentity_entry]

/-- A left-unipotent invariant paired product gives the value of the ordinary kernel
at the class of any representative. -/
theorem unequalIntegrand_mk_of_pair_invariant (nabs : K → ℝ) (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) K → ℂ) (W' : Langlands.GeneralLinear (t + 1) K → ℂ)
    (hpair : ∀ (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K)
      (g : Langlands.GeneralLinear (t + 1) K),
        W (padGL (Nat.succ_le_succ h.le) (u.val * g)) * W' (u.val * g) =
          W (padGL (Nat.succ_le_succ h.le) g) * W' g)
    (s : ℂ) (g : Langlands.GeneralLinear (t + 1) K) :
    ArchimedeanLocal.unequalIntegrand nabs h W W' s (Quotient.mk'' g) =
      W (padGL (Nat.succ_le_succ h.le) g) * W' g *
        ArchimedeanLocal.detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2) := by
  let q : LeftUnipotentQuotient t K := Quotient.mk'' g
  have hq : Quotient.mk'' q.out = Quotient.mk'' g := Quotient.out_eq q
  have hu : q.out * g⁻¹ ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) K :=
    (LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hq.symm
  let u : Langlands.GeneralLinear.upperUnipotent (t + 1) K := ⟨q.out * g⁻¹, hu⟩
  have he : q.out = u.val * g := by dsimp [u]; group
  change W (padGL (Nat.succ_le_succ h.le) q.out) * W' q.out *
    ArchimedeanLocal.detPower nabs q.out (s - ((r - t : ℕ) : ℂ) / 2) = _
  rw [he, hpair, local_detPower_unipotent_mul]

variable [TopologicalSpace K]

/-- The standard and inverse Whittaker characters cancel on the smaller unipotent
subgroup embedded by ordinary block-zero padding. -/
theorem unequalPair_invariant {k : ℕ} (hr : r = t + (0 + k + 1))
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ t) (h : t < r)
    (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K)
    (g : Langlands.GeneralLinear (t + 1) K) :
    W.val (padGL (Nat.succ_le_succ h.le) (u.val * g)) * W'.val (u.val * g) =
      W.val (padGL (Nat.succ_le_succ h.le) g) * W'.val g := by
  subst r
  simp only [padGL_eq_appendIdentity k h]
  rw [map_mul, ← appendUnipotent_val u (0 + k + 1), W.property, W'.property,
    appendUnipotent_character]
  change ((Whittaker.standardCharacter ψ t u : ℂ) * _) *
    ((((Whittaker.standardCharacter ψ t u)⁻¹ : ℂˣ) : ℂ) * _) = _
  rw [mul_mul_mul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- The ordinary local kernel with zero rectangular rows integrates to the actual
JPSS block-zero integral. -/
theorem unequalIntegral_eq_blockZero {k : ℕ} (hr : r = t + (0 + k + 1)) (h : t < r)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K) (abv : AbsoluteValue K ℝ)
    [IsTopologicalRing K] [MeasurableSpace K]
    [MeasurableSpace (LeftUnipotentQuotient t K)]
    [MeasurableSingletonClass (Matrix (Fin 0) (Fin (t + 1)) K)]
    (μ : Measure (LeftUnipotentQuotient t K)) (ν : HarmonicAnalysis.AdditiveHaarMeasure K)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ t) (s : ℂ) :
    ArchimedeanLocal.unequalIntegral abv μ h W.val W'.val s =
      unequalRankIntegralAt 0 k hr ψ abv μ (rectangularMeasure ν 0 (t + 1)) W W' s := by
  subst r
  unfold ArchimedeanLocal.unequalIntegral unequalRankIntegralAt
  simp only [rectangularMeasure_zero_rows, unequalRankIntegral]
  simp only [integral_dirac]
  apply integral_congr_ae
  filter_upwards [] with q
  have hgap : t + (0 + k + 1) - t = 0 + k + 1 := by omega
  calc
    _ = unequalRankIntegrand ψ abv 0 k W W' s 0 (Quotient.mk'' q.out) := by
      rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows]
      simp only [ArchimedeanLocal.unequalIntegrand, padGL_eq_appendIdentity k h, hgap,
        determinantWeight_eq_detPower]
    _ = _ := congrArg (unequalRankIntegrand ψ abv 0 k W W' s 0) (Quotient.out_eq q)

end Local

/-- A paired Whittaker product on the partial domain implies the product of the
ordinary unequal-rank quotient integrands. -/
def PairedWhittakerIntegrandProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] {r t : ℕ} (h : t < r)
    (S : Finset (FinitePlace F)) (κ : ℂ)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ)
    (WR : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (WC : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (WC' : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (WS : ∀ v : S, FiniteLocalGL F (r + 1) v.1 → ℂ)
    (WS' : ∀ v : S, FiniteLocalGL F (t + 1) v.1 → ℂ),
    let hp := Nat.succ_le_succ h.le
    (∀ v (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) g,
      WR v (padGL hp (u.val * g)) * WR' v (u.val * g) = WR v (padGL hp g) * WR' v g) →
    (∀ w (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ) g,
      WC w (padGL hp (u.val * g)) * WC' w (u.val * g) = WC w (padGL hp g) * WC' w g) →
    (∀ (v : S) (u : Langlands.GeneralLinear.upperUnipotent (t + 1) (FiniteCompletion F v.1)) g,
      WS v (padGL hp (u.val * g)) * WS' v (u.val * g) = WS v (padGL hp g) * WS' v g) →
    (∀ g ∈ unipotentIntegralOutside F (t + 1) S,
      W (pad F hp g) * W' g = κ *
        ((∏ v, WR v (padGL hp (realComponent F (t + 1) v g)) * WR' v (realComponent F (t + 1) v g)) *
        (∏ w, WC w (padGL hp (complexComponent F (t + 1) w g)) * WC' w (complexComponent F (t + 1) w g)) *
        ∏ v : S, WS v (padGL hp (finiteComponent F (t + 1) v.1 g)) * WS' v (finiteComponent F (t + 1) v.1 g))) →
    ∀ (s : ℂ) (q : WhittakerQuotient F (t + 1)),
      q ∈ unipotentIntegralClasses F (t + 1) S →
      unequalWhittakerIntegrand F h W W' s q = κ *
        ((∏ v, ArchimedeanLocal.realUnequalIntegrand h (WR v) (WR' v) s
          (realQuotientProjection F t v q)) *
        (∏ w, ArchimedeanLocal.complexUnequalIntegrand h (WC w) (WC' w) s
          (complexQuotientProjection F t w q)) *
        ∏ v : S, ArchimedeanLocal.unequalIntegrand
          (RankinSelberg.normalizedAbsoluteValue (CompletionPadic.padicField v.1).canonicalTopologicalData)
          h (WS v) (WS' v) s (finiteQuotientProjection F t v.1 q))

/-- Multiply the paired Whittaker product by the determinant product and pass to the
local unipotent quotients using invariance. -/
theorem pairedWhittakerIntegrandProduct : PairedWhittakerIntegrandProductStatement.{u} := by
  intro F _ _ r t h S κ W W' WR WR' WC WC' WS WS' hp hR hC hS hW s q hq
  have hg : q.out ∈ unipotentIntegralOutside F (t + 1) S := hq
  have heR (v : {v : InfinitePlace F // v.IsReal}) :=
    unequalIntegrand_mk_of_pair_invariant ArchimedeanLocal.realNormalizedAbs h
    (WR v) (WR' v) (hR v) s (realComponent F (t + 1) v q.out)
  have heC (w : {v : InfinitePlace F // v.IsComplex}) :=
    unequalIntegrand_mk_of_pair_invariant ArchimedeanLocal.complexNormalizedAbs h
    (WC w) (WC' w) (hC w) s (complexComponent F (t + 1) w q.out)
  have heS (v : S) := unequalIntegrand_mk_of_pair_invariant
    (RankinSelberg.normalizedAbsoluteValue (CompletionPadic.padicField v.1).canonicalTopologicalData)
    h (WS v) (WS' v) (hS v) s (finiteComponent F (t + 1) v.1 q.out)
  rw [Unfolding.unequalWhittakerIntegrand_eq, Unfolding.ordinaryKernel, hW q.out hg,
    DeterminantProducts.detPower_product F (t + 1) S q.out hg]
  simp only [ArchimedeanLocal.realUnequalIntegrand, ArchimedeanLocal.complexUnequalIntegrand,
    realQuotientProjection, complexQuotientProjection, finiteQuotientProjection,
    heR, heC, heS, Finset.prod_mul_distrib]
  ring

end Langlands.Global.RankinSelbergGlobal.UnequalIntegrandProducts
