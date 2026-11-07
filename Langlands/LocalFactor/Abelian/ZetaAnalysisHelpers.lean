import Langlands.LocalFactor.Abelian.LocalAnalysisHelpers
import Langlands.HarmonicAnalysis.PadicLatticeHaarProof
import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

/-- The multiplicative valuation of a nonzero element records its additive order. -/
theorem discreteValuation_eq_exp_neg_ord {x : F.Carrier} (hx : x ≠ 0) :
    T.discreteValuation x = WithZero.exp (-T.ord x) := by
  simpa only [PadicField.TopologicalData.ord, neg_neg] using
    (WithZero.exp_log ((map_ne_zero T.discreteValuation).mpr hx)).symm

/-- The order-zero annulus is the difference of two adjacent valuation lattices. -/
theorem integralUnits_eq_lattice_diff :
    integralUnits T = (T.additiveLattice 0 : Set F.Carrier) \
      (T.additiveLattice (-1) : Set F.Carrier) := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [integralUnits]
  · change (x ≠ 0 ∧ T.ord x = 0) ↔
      T.discreteValuation x ≤ WithZero.exp 0 ∧
        ¬T.discreteValuation x ≤ WithZero.exp (-1)
    rw [discreteValuation_eq_exp_neg_ord T hx]
    simp only [ne_eq, hx, not_false_eq_true, true_and, WithZero.exp_le_exp, not_le]
    omega

/-- The integer-ring set is exactly the zeroth valuation lattice. -/
theorem integerRing_eq_lattice_zero :
    integerRing T = (T.additiveLattice 0 : Set F.Carrier) := by
  rw [integerRing_eq]
  exact Set.ext (fun x => (T.mem_additiveLattice_zero x).symm)

/-- Finite positive masses and the exact integral-unit normalization at any Haar measure. -/
theorem haar_integer_units_masses (μ : LocalHaar) :
    letI := T.topology
    letI := borel F.Carrier
    0 < (μ.measure (integerRing T)).toReal ∧
    0 < (μ.measure (integralUnits T)).toReal ∧
    (μ.measure (integralUnits T)).toReal =
      (1 - (T.residueCardinality : ℝ)⁻¹) * (μ.measure (integerRing T)).toReal := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have hmass := (HarmonicAnalysis.padicLatticeHaar F T).1 μ
  have hzero := hmass 0
  have hneg := hmass (-1)
  have hsub : (T.additiveLattice (-1) : Set F.Carrier) ⊆ T.additiveLattice 0 :=
    T.additiveLattice_mono (by omega)
  have heq : (μ.measure (integralUnits T)).toReal =
      (1 - (T.residueCardinality : ℝ)⁻¹) * (μ.measure (integerRing T)).toReal := by
    rw [integralUnits_eq_lattice_diff, ← measureReal_def,
      measureReal_sdiff hsub (T.isOpen_additiveLattice (-1)).measurableSet hzero.1.ne]
    rw [measureReal_def, measureReal_def, hneg.2.2, integerRing_eq_lattice_zero]
    simp only [zpow_neg_one]
    ring
  have hO : 0 < (μ.measure (integerRing T)).toReal := by
    rw [integerRing_eq_lattice_zero]
    exact hzero.2.1
  refine ⟨hO, ?_, heq⟩
  rw [heq]
  exact mul_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀
    (by exact_mod_cast T.residueCardinality_gt_one))) hO

/-- The Euler denominator is entire in the actual spectral parameter. -/
theorem analyticAt_euler_denominator (π : F.Carrierˣ) (χ : Character) (s : ℂ) :
    AnalyticAt ℂ (fun z => 1 - (χ π : ℂ) * spectralVariable T z) s := by
  unfold spectralVariable
  fun_prop

/-- The totalized reciprocal Euler factor is in meromorphic normal form. -/
theorem lFactorAt_meromorphicNFOn (π : F.Carrierˣ) (χ : Character) (a : ℕ) :
    MeromorphicNFOn (lFactorAt T π χ a) Set.univ := by
  classical
  by_cases ha : a = 0
  · intro s _
    change MeromorphicNFAt (fun z => lFactorAt T π χ a z) s
    simp only [lFactorAt, ha, ite_true]
    exact (analyticAt_euler_denominator T π χ s).meromorphicNFAt.inv
  · intro s _
    change MeromorphicNFAt (fun z => lFactorAt T π χ a z) s
    simpa only [lFactorAt, ha, ite_false] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s).meromorphicNFAt

/-- At every regular point the Euler factor has a nonzero finite value. -/
theorem lFactorAt_ne_zero_of_regular (π : F.Carrierˣ) (χ : Character) (a : ℕ)
    (s : ℂ) (hs : RegularPoint T π χ a s) : lFactorAt T π χ a s ≠ 0 := by
  classical
  by_cases ha : a = 0
  · simpa only [lFactorAt, ha, ite_true] using
      inv_ne_zero (hs.resolve_left (not_not.mpr ha))
  · simp [lFactorAt, ha]

end Langlands.LocalFactor.PadicAbelian
