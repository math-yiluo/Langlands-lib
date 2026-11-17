import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Representation.RankinSelberg.EqualRankFunctionalEquationProof

/-! # Finite equal-rank data nonvanishing on every right half-plane -/

noncomputable section
universe uK uV uW
open MeasureTheory Langlands.RankinSelberg Langlands.HarmonicAnalysis
open Langlands.Whittaker Langlands.GeneralLinear Langlands.QuotientIntegration
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.EqualNonvanishing

/-- A nonzero rational continuation gives nonzero values arbitrarily far right. -/
theorem nonvanishing_on_right_of_rational {q : ℕ} (hq : 1 < q)
    {f : ℂ → ℂ} {R : RationalFunctions} (hR : R ≠ 0)
    (hf : HasRationalContinuation q f R) :
    ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ f s ≠ 0 := by
  obtain ⟨b, hb⟩ := hf
  intro a
  obtain ⟨t, ht, hn⟩ := (Set.Ioi_infinite (max a b)).exists_notMem_finite
    (finite_spectralPoint_roots hq (RatFunc.num_ne_zero hR))
  have ha : a < t := lt_of_le_of_lt (le_max_left a b) ht
  have hbt : b < t := lt_of_le_of_lt (le_max_right a b) ht
  obtain ⟨hd, he⟩ := hb (t : ℂ) hbt
  refine ⟨t, ha, ?_⟩
  rw [he, EqualSemilocalReduction.ratEval_eq_div]
  exact div_ne_zero hn hd

/-- The normalized functional equation carries nonzero ordinary continuation
to nonzero dual continuation. -/
theorem dual_ne_zero_of_normalized {q : ℕ} (hq : 1 < q)
    {P Pd : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {m : ℤ}
    {R Rd : RationalFunctions} (hP : P ≠ 0) (hR : R ≠ 0)
    (hFE : NormalizedFunctionalEquation q P Pd ζ c e m R Rd) : Rd ≠ 0 := by
  intro hzero
  subst Rd
  have hbad := ((finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
    (finite_spectralPoint_roots hq (RatFunc.num_ne_zero hR))).union
      (finite_spectralPoint_roots hq hP)
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
  obtain ⟨⟨hd, hn⟩, hp⟩ := ht
  have hev : R.eval (RingHom.id ℂ) (spectralPoint q (t : ℂ)) ≠ 0 := by
    rw [EqualSemilocalReduction.ratEval_eq_div]
    exact div_ne_zero hn hd
  have h := hFE (t : ℂ) hd (by simp)
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrhs := mul_ne_zero
    (mul_ne_zero (pow_ne_zero e ζ.ne_zero) (epsilonMonomial_ne_zero q hq0 c m (t : ℂ)))
    (mul_ne_zero hp hev)
  exact hrhs (by simpa using h.symm)

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance : MeasurableSpace K.Carrier := borel K.Carrier
local instance : BorelSpace K.Carrier := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := borel _
local instance (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r K.Carrier) := ⟨rfl⟩

/-- For fixed nonzero Whittaker functionals, actual equal-rank local data
have nonzero ordinary and dual integrals on every right half-plane. -/
def PadicEqualNonvanishingTestStatement : Prop :=
  ∀ (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (ν : Correspondence.LocalAdditiveHaarMeasure K), Correspondence.IsSelfDualMeasure K ψ ν →
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) W),
    IsOfWhittakerType r (standardCharacter ψ r) π →
    IsOfWhittakerType r (inverseStandardCharacter ψ r) σ →
  ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ r σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
    ∃ D : EqualLocalTestData K ψ ν π σ,
      D.ℓ = ℓ ∧ D.ℓ' = ℓ' ∧
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality D.integral 1 ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.integral s ≠ 0) ∧
      ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.dualIntegral s ≠ 0

/-- The local unit-value and functional-equation theorems give the desired data. -/
theorem padicEqualNonvanishingTest : PadicEqualNonvanishingTestStatement.{uK,uV,uW} K := by
  intro ψ ν hν r V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hμ := unipotentQuotientHaar_isCompatible K.Carrier r
  have hone := equalRankUnitValue K K.canonicalTopologicalData r ψ
    (unipotentQuotientHaar K.Carrier r) hμ V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨f, f', Φ, h1⟩ := hone
  obtain ⟨ζ, c, m, P, Pd, -, hP, -, hFE⟩ :=
    equalRankFunctionalEquation K K.canonicalTopologicalData r ψ
      (unipotentQuotientHaar K.Carrier r) hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨Φhat, R, Rd, hpair, hR, hRd, hN⟩ := hFE f f' Φ
  have hq := K.canonicalTopologicalData.residueCardinality_gt_one
  have hR1 : R = 1 := hR.unique hq h1
  have hR0 : R ≠ 0 := by rw [hR1]; exact one_ne_zero
  have hRd0 : Rd ≠ 0 := dual_ne_zero_of_normalized hq hP.polynomial_ne_zero hR0 hN
  let D : EqualLocalTestData K ψ ν π σ :=
    ⟨ℓ, ℓ', hℓ, hℓ', f, f', Φ, Φhat, hpair⟩
  refine ⟨D, rfl, rfl, h1, ?_, ?_⟩
  · exact nonvanishing_on_right_of_rational hq one_ne_zero h1
  · exact nonvanishing_on_right_of_rational hq hRd0 hRd

end Padic

end Langlands.Global.RankinSelbergGlobal.EqualNonvanishing
