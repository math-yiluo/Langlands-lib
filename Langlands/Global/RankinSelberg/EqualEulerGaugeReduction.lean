import Langlands.Global.RankinSelberg.EqualEulerFactorizationReduction
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition
import Langlands.Global.RankinSelberg.EqualGaugeSpecialization

/-! # The equal-rank partial Euler factorization from the Whittaker–Schwartz bound

`EqualEulerFactorizationStatement` follows from the single remaining analytic input
`EqualWhittakerSchwartzStatement`: the weighted Whittaker–Schwartz integral of every cuspidal
realization is finite in a right half-plane. All other inputs of
`equalEulerFactorizationReduction` are now published proofs: the spherical factorization (A)
`UnramifiedWhittaker.unramifiedWhittakerFactorization`, the one-place cell decomposition
`whittakerCellDecomposition`, and the passage from the Whittaker–Schwartz bound to the primal
gauge premise `equalGaugeReduction`. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- **The reduction.** The Whittaker–Schwartz bound for every cuspidal realization implies the
equal-rank partial Euler factorization. -/
def EqualEulerGaugeReductionStatement : Prop :=
  EqualWhittakerSchwartzStatement.{u} → EqualEulerFactorizationStatement.{u, uQ}

open EqualEulerReduction in
/-- The primal gauge premise `EqualWhittakerGaugeIntegrable` for every equal-rank pair implies the
equal-rank partial Euler factorization. This is the body of `equalEulerFactorizationReduction`,
with (A) and the cell decomposition taken from their published proofs and the integrability bound
from `integrable_equalWhittakerIntegrand_of_gauge` instead of `EqualUnfoldingStatement`. -/
theorem equalEulerFactorization_of_gauge
    (hG : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
      (T T' : Automorphic.CuspidalOperatorRealization F r), EqualWhittakerGaugeIntegrable F T T') :
    EqualEulerFactorizationStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r T T' P P' S hP hP' hψS
  have hA := UnramifiedWhittaker.unramifiedWhittakerFactorization.{u, uQ}
  have hB := whittakerCellDecomposition.{u}
  obtain ⟨C0, -, hC0⟩ := integrable_equalWhittakerIntegrand_of_gauge F (hG F r T T')
  obtain ⟨σ2, hσ2⟩ := exists_partialEulerFactor_convergence P P' hP hP'
  obtain ⟨C, hC⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨C', hC'⟩ := exists_hasSatakeBound_presentation T' P'
  refine ⟨max C0 (max σ2 (EqualEulerLocal.localRadius r C C')), ?_⟩
  intro x x' Φ hx hx' hΦs hΦ W W' s hs
  have hs0 : C0 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : σ2 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsl : EqualEulerLocal.localRadius r C C' < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hint := hC0 ψ.complex (isStandardAdditiveCharacter_of_unitary ψ hψ) x x' Φ hΦs s hs0
  obtain ⟨hsum, hprod⟩ := hσ2 s hs2
  refine ⟨hint, hsum, partialEulerProduct P P' hP hP' s, hprod, ?_⟩
  rw [partialEqualWhittakerIntegral_eq_setIntegral]
  exact (integral_eq_hasProd_mul_setIntegral hint hprod
    (fun A hSA v hvA => setIntegral_insert hA hB ψ hψ hP hP' hψS hC hC' hx hx' hΦ hsl hint
      hSA v hvA)).trans (mul_comm _ _)

/-- Proof of `EqualEulerGaugeReductionStatement`: `equalGaugeReduction` turns the
Whittaker–Schwartz bound into the primal gauge premise for every pair. -/
theorem equalEulerGaugeReduction : EqualEulerGaugeReductionStatement.{u, uQ} :=
  fun h => equalEulerFactorization_of_gauge (equalGaugeReduction h)

/-- The first conjunct of `EqualUnfoldingGaugeStatement` suffices. -/
theorem equalEulerFactorization_of_equalUnfoldingGauge (h : EqualUnfoldingGaugeStatement.{u}) :
    EqualEulerFactorizationStatement.{u, uQ} :=
  equalEulerFactorization_of_gauge h.1

/-- The general estimate `WhittakerSchwartzGaugeStatement` suffices, through
`equalGaugeSpecialization`. -/
theorem equalEulerFactorization_of_whittakerSchwartzGauge
    (h : WhittakerSchwartzGaugeStatement.{u}) : EqualEulerFactorizationStatement.{u, uQ} :=
  equalEulerGaugeReduction (equalGaugeSpecialization h)

end Langlands.Global.RankinSelbergGlobal
