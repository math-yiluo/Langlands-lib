import Langlands.Representation.RankinSelberg.EqualRankUnitNormalization
import Langlands.Group.GL.Mirabolic
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Assembly of compact equal-rank test data

Concrete mirabolic product, right invariance and exact row-test hypotheses
identify the actual integrand with a quotient-set indicator. Existence of
such data and positivity of the quotient volume are separate obligations.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped Pointwise

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- The image in the actual left-unipotent quotient of a mirabolic set
multiplied on the right by a subgroup. No normalization relation is imposed. -/
def equalRankCompactSet (C : Set (GeneralLinear.mirabolic n F))
    (J : Subgroup (Langlands.GeneralLinear (n + 1) F)) :
    Set (LeftUnipotentQuotient n F) :=
  leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) ''
    ((fun p : GeneralLinear.mirabolic n F => p.val) '' C * (J : Set _))

/-- Explicit sufficient conditions for the compact equal-rank assembly step.
These conditions assert no existence of tests, vectors, or quotient measures. -/
def IsEqualRankCompactTest (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (C : Set (GeneralLinear.mirabolic n F))
    (J : Subgroup (Langlands.GeneralLinear (n + 1) F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) : Prop :=
  (∀ p : GeneralLinear.mirabolic n F,
    W.val p.val * W'.val p.val =
      (leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) ''
        ((fun c : GeneralLinear.mirabolic n F => c.val) '' C)).indicator
        (fun _ => (1 : ℂ))
        (leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) p.val)) ∧
  (∀ g : Langlands.GeneralLinear (n + 1) F, ∀ j : J,
    W.val (g * j.val) * W'.val (g * j.val) = W.val g * W'.val g) ∧
  (∀ y, Φ y = (lastRow '' (J : Set _)).indicator (fun _ => (1 : ℂ)) y) ∧
  (∀ g : Langlands.GeneralLinear (n + 1) F,
    lastRow g ∈ lastRow '' (J : Set _) ↔
      ∃ p : GeneralLinear.mirabolic n F, ∃ j : J, g = p.val * j.val) ∧
  (∀ c ∈ C, abv (Matrix.det c.val.val) = 1) ∧
  (∀ j : J, abv (Matrix.det j.val.val) = 1)

omit [TopologicalSpace F] in
/-- The right thickening contains the subgroup orbit when the mirabolic set
contains the identity. -/
theorem subgroup_orbit_subset_equalRankCompactSet
    (C : Set (GeneralLinear.mirabolic n F))
    (J : Subgroup (Langlands.GeneralLinear (n + 1) F)) (hC : 1 ∈ C) :
    leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) '' (J : Set _) ⊆
      equalRankCompactSet C J := by
  rintro x ⟨j, hj, rfl⟩
  refine ⟨j, Set.mem_mul.mpr ⟨1, ?_, j, hj, one_mul j⟩, rfl⟩
  exact ⟨1, hC, rfl⟩

section Topology

variable [IsTopologicalRing F]

/-- A compact mirabolic set and compact right subgroup have compact quotient image. -/
theorem isCompact_equalRankCompactSet
    {C : Set (GeneralLinear.mirabolic n F)}
    {J : Subgroup (Langlands.GeneralLinear (n + 1) F)}
    (hC : IsCompact C)
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F))) :
    IsCompact (equalRankCompactSet C J) :=
  ((hC.image continuous_subtype_val).mul hJ).image
    (leftQuotient_isOpenQuotientMap _).continuous

/-- Multiplication by an open right subgroup makes the quotient image open,
without any subgroup-normalization assumption. -/
theorem isOpen_equalRankCompactSet
    (C : Set (GeneralLinear.mirabolic n F))
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F)) :
    IsOpen (equalRankCompactSet C J.toSubgroup) :=
  (leftQuotient_isOpenQuotientMap _).isOpenMap _ J.isOpen.mul_left

end Topology

/-- The concrete test hypotheses identify the actual integrand at every
spectral parameter with the indicator of the right-thickened compact set. -/
theorem IsEqualRankCompactTest.integrand_eq
    {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {C : Set (GeneralLinear.mirabolic n F)}
    {J : Subgroup (Langlands.GeneralLinear (n + 1) F)}
    {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)}
    (h : IsEqualRankCompactTest ψ abv C J W W' Φ) (s : ℂ) :
    equalRankIntegrand ψ abv W W' Φ s =
      (equalRankCompactSet C J).indicator (fun _ => (1 : ℂ)) := by
  classical
  rcases h with ⟨hprod, hright, hΦ, hrow, hCdet, hJdet⟩
  funext x
  induction x using Quotient.inductionOn with
  | h g =>
    change equalRankIntegrand ψ abv W W' Φ s
        (leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) g) =
      (equalRankCompactSet C J).indicator (fun _ => (1 : ℂ))
        (leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) g)
    by_cases hx : leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) g ∈
        equalRankCompactSet C J
    · rw [Set.indicator_of_mem hx]
      rcases hx with ⟨z, hz, hq⟩
      rcases Set.mem_mul.mp hz with ⟨c, hc, j, hj, rfl⟩
      rcases hc with ⟨c, hc, rfl⟩
      rw [← hq]
      change W.val (c.val * j) * W'.val (c.val * j) *
        Φ (lastRow (c.val * j)) * determinantWeight abv (c.val * j) s = 1
      rw [hright c.val ⟨j, hj⟩, hprod c]
      have hbase : leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) c.val ∈
          leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) ''
            ((fun p : GeneralLinear.mirabolic n F => p.val) '' C) :=
        ⟨c.val, ⟨c, hc, rfl⟩, rfl⟩
      have hr : lastRow (c.val * j) ∈ lastRow '' (J : Set _) :=
        (hrow _).2 ⟨c, ⟨j, hj⟩, rfl⟩
      rw [Set.indicator_of_mem hbase, hΦ, Set.indicator_of_mem hr]
      simp only [one_mul, determinantWeight]
      change (abv (Matrix.det (c.val.val * j.val)) : ℂ) ^ s = 1
      rw [Matrix.det_mul, map_mul, hCdet c hc, hJdet ⟨j, hj⟩]
      simp
    · rw [Set.indicator_of_notMem hx]
      change W.val g * W'.val g * Φ (lastRow g) * determinantWeight abv g s = 0
      by_cases hr : lastRow g ∈ lastRow '' (J : Set _)
      · obtain ⟨p, j, rfl⟩ := (hrow g).1 hr
        have hp : leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) p.val ∉
            leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) ''
              ((fun c : GeneralLinear.mirabolic n F => c.val) '' C) := by
          rintro ⟨c, ⟨c, hc, rfl⟩, hcp⟩
          apply hx
          refine ⟨c.val * j.val, Set.mem_mul.mpr
            ⟨c.val, ⟨c, hc, rfl⟩, j.val, j.property, rfl⟩, ?_⟩
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
            (QuotientGroup.rightRel_apply.mp (Quotient.exact hcp))
        rw [hright p.val j, hprod p, Set.indicator_of_notMem hp, zero_mul, zero_mul]
      · rw [hΦ, Set.indicator_of_notMem hr, mul_zero, zero_mul]

section Integration

variable [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- The total actual integral of the assembled tests is the real mass of the
quotient set, viewed as a complex number. This identity alone needs no finiteness. -/
theorem IsEqualRankCompactTest.integral_eq
    {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {C : Set (GeneralLinear.mirabolic n F)}
    {J : Subgroup (Langlands.GeneralLinear (n + 1) F)}
    {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)}
    (h : IsEqualRankCompactTest ψ abv C J W W' Φ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (hmeas : MeasurableSet (equalRankCompactSet C J)) (s : ℂ) :
    equalRankIntegral ψ abv μ W W' Φ s = ((μ (equalRankCompactSet C J)).toReal : ℂ) := by
  rw [equalRankIntegral, h.integrand_eq s, integral_indicator_const _ hmeas]
  simp [Measure.real, Complex.real_smul]

/-- Finite quotient volume gives convergence for these particular test data
at every spectral parameter. It asserts no general analytic result. -/
theorem IsEqualRankCompactTest.converges
    {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {C : Set (GeneralLinear.mirabolic n F)}
    {J : Subgroup (Langlands.GeneralLinear (n + 1) F)}
    {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)}
    (h : IsEqualRankCompactTest ψ abv C J W W' Φ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (hmeas : MeasurableSet (equalRankCompactSet C J))
    (hfin : μ (equalRankCompactSet C J) < ⊤) (s : ℂ) :
    EqualRankConverges ψ abv μ W W' Φ s := by
  change Integrable _ μ
  rw [h.integrand_eq s]
  exact (integrableOn_const hfin.ne).integrable_indicator hmeas

/-- Actual coefficient vectors satisfying the explicit compact-test conditions
and having positive finite quotient volume give literal rational value one. -/
theorem one_mem_equalRankRationalValues_of_compact_test
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (C : Set (GeneralLinear.mirabolic n F))
    (J : Subgroup (Langlands.GeneralLinear (n + 1) F))
    (h : IsEqualRankCompactTest ψ abv C J f.val f'.val Φ)
    (hmeas : MeasurableSet (equalRankCompactSet C J))
    (hpos : 0 < μ (equalRankCompactSet C J))
    (hfin : μ (equalRankCompactSet C J) < ⊤) :
    (1 : RationalFunctions) ∈ equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  refine one_mem_equalRankRationalValues_of_nonzero_constant q ψ abv μ π σ ℓ ℓ'
    ((μ (equalRankCompactSet C J)).toReal : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (ENNReal.toReal_pos hpos.ne' hfin.ne)))
    f f' Φ 0 ?_
  intro s _
  exact h.integral_eq μ hmeas s

end Integration

end Langlands.RankinSelberg
