import Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
import Langlands.Analysis.Local.QuotientAutomorphismProof

/-! Automorphism covariance of the actual finite-fiber compact integral. -/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open Langlands.HarmonicAnalysis
open scoped NNReal ENNReal

universe uG uV uW uX

section Coinvariants

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (H : Subgroup G) (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)

/-- The two full-group relation quotients have the same vector classes:
the restricting automorphism runs through all of `H`. -/
def automorphismCoinvariantsEquiv (σ : Representation ℂ H V) :
    Representation.Coinvariants (automorphismInducing H α hα σ) ≃ₗ[ℂ]
      Representation.Coinvariants σ where
  __ := Representation.Coinvariants.lift (automorphismInducing H α hα σ)
    (Representation.Coinvariants.mk σ) (fun h => LinearMap.ext fun v =>
      Representation.Coinvariants.mk_self_apply σ
        (QuotientIntegration.subgroupAutomorphism H α hα h) v)
  invFun := Representation.Coinvariants.lift σ
    (Representation.Coinvariants.mk (automorphismInducing H α hα σ)) (fun h => by
      apply LinearMap.ext
      intro v
      change Representation.Coinvariants.mk (automorphismInducing H α hα σ)
        (σ h v) = Representation.Coinvariants.mk (automorphismInducing H α hα σ) v
      let e := QuotientIntegration.subgroupAutomorphism H α hα
      have key := Representation.Coinvariants.mk_self_apply
        (automorphismInducing H α hα σ) (e.symm h) v
      change Representation.Coinvariants.mk (automorphismInducing H α hα σ)
        (σ (e (e.symm h)) v) = _ at key
      simpa only [e.apply_symm_apply] using key)
  left_inv z := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
      (automorphismInducing H α hα σ) z
    rfl
  right_inv z := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σ z
    rfl

@[simp]
theorem automorphismCoinvariantsEquiv_mk (σ : Representation ℂ H V) (v : V) :
    automorphismCoinvariantsEquiv H α hα σ
        (Representation.Coinvariants.mk (automorphismInducing H α hα σ) v) =
      Representation.Coinvariants.mk σ v := rfl

/-- The same transport is natural for intertwiners in independent universes. -/
theorem automorphismCoinvariantsEquiv_natural
    {σ : Representation ℂ H V} {τ : Representation ℂ H W}
    (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants (automorphismInducing H α hα σ)) :
    automorphismCoinvariantsEquiv H α hα τ
        (Representation.Coinvariants.map (automorphismInducing H α hα σ)
          (automorphismInducing H α hα τ) (automorphismInducingMap H α hα T) z) =
      Representation.Coinvariants.map σ τ T
        (automorphismCoinvariantsEquiv H α hα σ z) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
    (automorphismInducing H α hα σ) z
  rfl

end Coinvariants

section MeasureScaling

variable {X : Type uX} [MeasurableSpace X]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A finite nonnegative scalar on the measure scales the actual fiber sum.
The totalized formula also covers infinite fiber measures. -/
theorem algebraicIntegral_smul_measure (ν : Measure X) (r : ℝ≥0)
    (f : SimpleFunc X V) :
    AlgebraicIntegral.integral ((r : ℝ≥0∞) • ν) f =
      (((r : ℝ) : ℂ)) • AlgebraicIntegral.integral ν f := by
  classical
  simp only [AlgebraicIntegral.integral, Finset.smul_sum, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.ofReal_mul, mul_smul]

end MeasureScaling

section Functions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (H : Subgroup G) (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)
  [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)]

/-- On the actual quotient simple functions, compact precomposition is the
quotient automorphism followed by the identity-on-vectors transport. -/
theorem quotientCoinvariantSimple_automorphism (σ : Representation ℂ H V)
    (f : CompactFunctions H σ) :
    (quotientCoinvariantSimple H (automorphismInducing H α hα σ)
        (precomposeCompactInducedEquiv H α hα σ f)).map
          (automorphismCoinvariantsEquiv H α hα σ).toLinearMap =
      (quotientCoinvariantSimple H σ f).comp
        (QuotientIntegration.quotientAutomorphism H α hα)
        (QuotientIntegration.quotientAutomorphism H α hα).continuous.measurable := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => rfl

end Functions

section IntegralCovariance

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  {μG : Measure G} {μH : Measure H}
  [IsHaarMeasure μG] [μG.Regular] [IsHaarMeasure μH] [μH.Regular]
  [IsMulRightInvariant μH]
  [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)]
  (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
  (hν : QuotientIntegration.IsCompatible H μG μH ν)
  (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)

include hH hν in
/-- Actual forward precomposition gives the subgroup-to-ambient Haar ratio. -/
theorem compactCoinvariantIntegral_automorphism (σ : Representation ℂ H V)
    (f : CompactFunctions H σ) :
    automorphismCoinvariantsEquiv H α hα σ
        (compactCoinvariantIntegral H (automorphismInducing H α hα σ) ν
          (precomposeCompactInducedEquiv H α hα σ f)) =
      ((((mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism H α hα) /
          mulEquivHaarChar α : ℝ≥0) : ℝ) : ℂ)) • compactCoinvariantIntegral H σ ν f := by
  let A := automorphismCoinvariantsEquiv H α hα σ
  let k := precomposeCompactInducedEquiv H α hα σ f
  let φ := quotientCoinvariantSimple H (automorphismInducing H α hα σ) k
  calc
    A (compactCoinvariantIntegral H (automorphismInducing H α hα σ) ν k) =
        AlgebraicIntegral.integral ν (φ.map A.toLinearMap) :=
      (AlgebraicIntegral.integral_linearMap φ
        (quotientCoinvariantSimple_finMeasSupp H (automorphismInducing H α hα σ) ν k)
        A.toLinearMap).symm
    _ = AlgebraicIntegral.integral ν
        ((quotientCoinvariantSimple H σ f).comp
          (QuotientIntegration.quotientAutomorphism H α hα)
          (QuotientIntegration.quotientAutomorphism H α hα).continuous.measurable) := by
      rw [quotientCoinvariantSimple_automorphism]
    _ = AlgebraicIntegral.integral
        (Measure.map (QuotientIntegration.quotientAutomorphism H α hα) ν)
        (quotientCoinvariantSimple H σ f) :=
      AlgebraicIntegral.integral_comp _ _ _
    _ = _ := by
      rw [hν.map_quotientAutomorphism H hH α hα, algebraicIntegral_smul_measure]
      rfl

end IntegralCovariance

/-- The unapplied covariance proposition at independent group and coefficient
universes, with no hypotheses added to the published statement. -/
theorem compactAutomorphismIntegralCovariance :
    CompactAutomorphismIntegralCovariance.{uG,uV} := by
  intro G _ _ _ _ _ _ _ H hH _ _ μG μH _ _ _ _ _ _ _ _ ν hν α hα
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  have : ν.Regular := hν.regular
  intro δG δH
  refine ⟨fun {V} _ _ σ => automorphismCoinvariantsEquiv H α hα σ, ?_, ?_, ?_⟩
  · intro V _ _ σ v
    rfl
  · intro V W _ _ _ _ σ τ T z
    exact automorphismCoinvariantsEquiv_natural H α hα T z
  · intro V _ _ σ f
    exact compactCoinvariantIntegral_automorphism H hH ν hν α hα σ f

end Langlands.Induction
