import Langlands.Global.CurvePlaceCompletionExtension
import Langlands.Global.FunctionFieldAbsoluteValueCompletions
import Mathlib.Analysis.AbsoluteValue.Equivalence

/-! # Finiteness and canonical completed products at actual curve places -/

noncomputable section

universe u v

open IsDedekindDomain
open scoped TensorProduct Valued

namespace Langlands.Global.CurvePlaceCompletedProduct

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]

/-- A real absolute value for the original discrete curve place. -/
def absoluteValue (q : AlgebraicCurve.Place k L) : AbsoluteValue L ℝ :=
  rankOneValuationAbsoluteValue q.adicValuation

theorem absoluteValue_nontrivial (q : AlgebraicCurve.Place k L) :
    (absoluteValue q).IsNontrivial :=
  rankOneValuationAbsoluteValue_nontrivial q.adicValuation

theorem absoluteValue_isEquiv_iff (q r : AlgebraicCurve.Place k L) :
    (absoluteValue q).IsEquiv (absoluteValue r) ↔ q = r := by
  refine ⟨fun h => ?_, fun h => h ▸ AbsoluteValue.IsEquiv.rfl⟩
  apply AlgebraicCurve.Place.ext
  have hv : q.adicValuation.IsEquiv r.adicValuation := by
    intro x y
    exact (rankOneValuationAbsoluteValue_le_iff q.adicValuation x y).symm.trans
      ((h x y).trans (rankOneValuationAbsoluteValue_le_iff r.adicValuation x y))
  exact q.adicValuation_valuationSubring.symm.trans
    (((Valuation.isEquiv_iff_valuationSubring _ _).mp hv).trans r.adicValuation_valuationSubring)

/-- The original field map, with the source absolute-value topology. -/
def withAbsEmbedding (q : AlgebraicCurve.Place k L) :
    WithAbs (absoluteValue q) →+* q.heightOneSpectrum.adicCompletion L :=
  (algebraMap L (q.heightOneSpectrum.adicCompletion L)).comp
    (WithAbs.equiv (absoluteValue q)).toRingHom

theorem continuous_withAbsEmbedding (q : AlgebraicCurve.Place k L) :
    Continuous (withAbsEmbedding q) := by
  let ha := rankOneValuationAbsoluteValue_nonarchimedean q.adicValuation
  let e₁ := absoluteValueWithValUniformEquiv (absoluteValue q) ha
  let h := rankOneValuationAbsoluteValue_valuation_isEquiv q.adicValuation
  let e₂ := h.uniformEquiv
  have hc := (UniformSpace.Completion.continuous_coe
    (α := WithVal q.adicValuation)).comp (e₂.continuous.comp e₁.continuous)
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L q.heightOneSpectrum).comp hc

theorem withAbsEmbedding_denseRange (q : AlgebraicCurve.Place k L) :
    DenseRange (withAbsEmbedding q) := by
  apply (q.heightOneSpectrum.denseRange_algebraMap L).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨(WithAbs.equiv (absoluteValue q)).symm x, rfl⟩

variable {ι : Type v}

/-- Weak approximation for any finite family of distinct actual curve places. -/
theorem denseRange_family [Finite ι] (q : ι → AlgebraicCurve.Place k L)
    (hq : Function.Injective q) :
    DenseRange (fun x : L => fun i => algebraMap L ((q i).heightOneSpectrum.adicCompletion L) x) := by
  have h := AbsoluteValue.denseRange_algebraMap_pi
    (v := fun i => absoluteValue (q i))
    (fun i => absoluteValue_nontrivial (q i))
    (fun i j hij he => hij (hq ((absoluteValue_isEquiv_iff (q i) (q j)).mp he)))
  have hd := DenseRange.piMap (fun i => withAbsEmbedding_denseRange (q i))
  exact hd.comp h (.piMap fun i => continuous_withAbsEmbedding (q i))

open scoped Langlands.Global.CurvePlaceCompletionExtension

variable (p : AlgebraicCurve.Place k K) (q : ι → CurvePlacesAbove k L p)

/-- The canonical simultaneous tensor map for the given family of actual upper places. -/
def familyTensorMap :
    p.heightOneSpectrum.adicCompletion K ⊗[K] L →ₐ[p.heightOneSpectrum.adicCompletion K]
      (∀ i, (q i).1.heightOneSpectrum.adicCompletion L) :=
  AlgHom.pi fun i => CurvePlaceCompletionExtension.tensorMap p (q i)

@[simp]
theorem familyTensorMap_tmul (a : p.heightOneSpectrum.adicCompletion K) (x : L) (i : ι) :
    familyTensorMap p q (a ⊗ₜ[K] x) i =
      CurvePlaceCompletionExtension.completionMap p (q i) a *
        algebraMap L ((q i).1.heightOneSpectrum.adicCompletion L) x := rfl

theorem familyTensorMap_denseRange [Finite ι] (hq : Function.Injective q) :
    DenseRange (familyTensorMap p q) := by
  have hq' : Function.Injective (fun i => (q i).1) := by
    intro i j h
    exact hq (Subtype.ext h)
  apply (denseRange_family (fun i => (q i).1) hq').mono
  rintro _ ⟨x, rfl⟩
  exact ⟨1 ⊗ₜ[K] x, by ext i; simp⟩

variable [FiniteDimensional K L]

/-- Finite-dimensional closedness upgrades simultaneous density to surjectivity. -/
theorem familyTensorMap_surjective [Finite ι] (hq : Function.Injective q) :
    Function.Surjective (familyTensorMap p q) := by
  let : (Valued.v : Valuation (p.heightOneSpectrum.adicCompletion K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NontriviallyNormedField (p.heightOneSpectrum.adicCompletion K) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  let f := (familyTensorMap p q).toLinearMap
  have hc : IsClosed (Set.range (familyTensorMap p q)) := by
    exact Submodule.closed_of_finiteDimensional
      (𝕜 := p.heightOneSpectrum.adicCompletion K) f.range
  exact Set.range_eq_univ.mp
    (hc.closure_eq.symm.trans (familyTensorMap_denseRange p q hq).closure_range)

/-- The sum of local degrees over distinct upper places is bounded by the global degree. -/
theorem familyLocalDegree_sum_le [Fintype ι] (hq : Function.Injective q) :
    (∑ i : ι, Module.finrank (p.heightOneSpectrum.adicCompletion K)
      ((q i).1.heightOneSpectrum.adicCompletion L)) ≤ Module.finrank K L := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (familyTensorMap p q).toLinearMap) (familyTensorMap_surjective p q hq)
  simpa only [Module.finrank_baseChange, Module.finrank_pi_fintype] using h

/-- A distinct finite family of upper places has at most the global degree many members. -/
theorem family_card_le [Fintype ι] (hq : Function.Injective q) :
    Fintype.card ι ≤ Module.finrank K L := by
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i : ι, Module.finrank (p.heightOneSpectrum.adicCompletion K)
        ((q i).1.heightOneSpectrum.adicCompletion L) :=
      Finset.sum_le_sum fun _ _ => Module.finrank_pos
    _ ≤ Module.finrank K L := familyLocalDegree_sum_le p q hq

end Langlands.Global.CurvePlaceCompletedProduct

namespace Langlands.Global

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [FiniteDimensional K L]

/-- There are only finitely many actual upper curve places in a finite field extension. -/
instance curvePlacesAbove_finite (p : AlgebraicCurve.Place k K) :
    Finite (CurvePlacesAbove k L p) := by
  classical
  by_contra h
  let : Infinite (CurvePlacesAbove k L p) := not_finite_iff_infinite.mp h
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq
    (CurvePlacesAbove k L p) (Module.finrank K L + 1)
  have hb := CurvePlaceCompletedProduct.family_card_le p
    (fun q : S => q.1) Subtype.val_injective
  rw [Fintype.card_coe, hS] at hb
  omega

/-- Enumerate the full upper-place subtype only after proving its finiteness. -/
instance curvePlacesAbove_fintype (p : AlgebraicCurve.Place k K) :
    Fintype (CurvePlacesAbove k L p) :=
  Fintype.ofFinite _

namespace CurvePlaceCompletedProduct

open scoped Langlands.Global.CurvePlaceCompletionExtension

variable (p : AlgebraicCurve.Place k K)

/-- The original canonical tensor map to every actual upper completion. -/
def allTensorMap :
    p.heightOneSpectrum.adicCompletion K ⊗[K] L →ₐ[p.heightOneSpectrum.adicCompletion K]
      (∀ q : CurvePlacesAbove k L p, q.1.heightOneSpectrum.adicCompletion L) :=
  familyTensorMap p id

omit [FiniteDimensional K L] in
@[simp]
theorem allTensorMap_tmul (a : p.heightOneSpectrum.adicCompletion K) (x : L)
    (q : CurvePlacesAbove k L p) :
    allTensorMap p (a ⊗ₜ[K] x) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (q.1.heightOneSpectrum.adicCompletion L) x := rfl

/-- Simultaneous surjectivity for the full actual upper-place subtype. -/
theorem allTensorMap_surjective : Function.Surjective (allTensorMap (L := L) p) :=
  familyTensorMap_surjective p
    (id : CurvePlacesAbove k L p → CurvePlacesAbove k L p) Function.injective_id

/-- The sum over every actual upper place is bounded by the original field degree. -/
theorem allLocalDegree_sum_le :
    (∑ q : CurvePlacesAbove k L p,
      Module.finrank (p.heightOneSpectrum.adicCompletion K)
        (q.1.heightOneSpectrum.adicCompletion L)) ≤ Module.finrank K L :=
  familyLocalDegree_sum_le p
    (id : CurvePlacesAbove k L p → CurvePlacesAbove k L p) Function.injective_id

end CurvePlaceCompletedProduct

end Langlands.Global
