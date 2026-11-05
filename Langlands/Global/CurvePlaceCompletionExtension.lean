import Langlands.Global.CurvePlaceExtension
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Actual completion embeddings at upper curve places -/

noncomputable section

universe u v w

open IsDedekindDomain
open scoped TensorProduct Valued

namespace Langlands.Global

variable (k : Type u) {K : Type v} (L : Type w)
  [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]

/-- All actual curve places whose valuation subring restricts to the given one. -/
def CurvePlacesAbove (p : AlgebraicCurve.Place k K) :=
  {q : AlgebraicCurve.Place k L //
    q.toValuationSubring.comap (algebraMap K L) = p.toValuationSubring}

namespace CurvePlaceCompletionExtension

variable {k L}
variable (p : AlgebraicCurve.Place k K) (q : CurvePlacesAbove k L p)

theorem mem_iff (x : K) :
    algebraMap K L x ∈ q.1.toValuationSubring ↔ x ∈ p.toValuationSubring := by
  change x ∈ q.1.toValuationSubring.comap (algebraMap K L) ↔ _
  rw [q.2]

/-- The original field embedding restricted to the original valuation rings. -/
def integersMap : p.toValuationSubring →+* q.1.toValuationSubring :=
  ((algebraMap K L).comp p.toValuationSubring.subtype).codRestrict _
    (fun x => (mem_iff p q x).mpr x.property)

scoped instance (priority := 50) : Algebra p.toValuationSubring L :=
  ((algebraMap K L).comp p.toValuationSubring.subtype).toAlgebra

scoped instance (priority := 50) : Algebra p.toValuationSubring q.1.toValuationSubring :=
  (integersMap p q).toAlgebra

scoped instance : IsScalarTower p.toValuationSubring K L :=
  .of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower p.toValuationSubring q.1.toValuationSubring L :=
  .of_algebraMap_eq fun _ => rfl

scoped instance : Module.IsTorsionFree p.toValuationSubring q.1.toValuationSubring :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    intro x y h
    apply Subtype.ext
    exact (algebraMap K L).injective (congrArg Subtype.val h))

scoped instance : q.1.heightOneSpectrum.asIdeal.LiesOver p.heightOneSpectrum.asIdeal := by
  constructor
  ext x
  change x ∈ IsLocalRing.maximalIdeal p.toValuationSubring ↔
    integersMap p q x ∈ IsLocalRing.maximalIdeal q.1.toValuationSubring
  rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  change (x : K) = 0 ∨ (x : K)⁻¹ ∉ p.toValuationSubring ↔
    algebraMap K L (x : K) = 0 ∨ (algebraMap K L (x : K))⁻¹ ∉ q.1.toValuationSubring
  rw [map_eq_zero, ← map_inv₀, mem_iff]

/-- The actual lower-to-upper valued-field embedding is uniformly continuous. -/
theorem uniformContinuous_withVal :
    UniformContinuous (algebraMap (WithVal p.adicValuation) (WithVal q.1.adicValuation)) :=
  HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L
    p.heightOneSpectrum q.1.heightOneSpectrum

/-- Extend the original field embedding to its actual adic completions. -/
def completionMap : (p.heightOneSpectrum.adicCompletion K) →+* (q.1.heightOneSpectrum.adicCompletion L) :=
  ((HeightOneSpectrum.adicCompletion.equiv L q.1.heightOneSpectrum).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal p.adicValuation) (WithVal q.1.adicValuation))
      (uniformContinuous_withVal p q).continuous)).comp
    (HeightOneSpectrum.adicCompletion.equiv K p.heightOneSpectrum).toRingHom

theorem continuous_completionMap : Continuous (completionMap p q) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L q.1.heightOneSpectrum).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K p.heightOneSpectrum))

@[simp]
theorem completionMap_algebraMap (x : K) :
    completionMap p q (algebraMap K ((p.heightOneSpectrum.adicCompletion K)) x) =
      algebraMap L ((q.1.heightOneSpectrum.adicCompletion L)) (algebraMap K L x) := by
  apply (HeightOneSpectrum.adicCompletion.equiv L q.1.heightOneSpectrum).injective
  exact UniformSpace.Completion.mapRingHom_coe
    (f := algebraMap (WithVal p.adicValuation) (WithVal q.1.adicValuation))
    (uniformContinuous_withVal p q).continuous (WithVal.toVal p.adicValuation x)

scoped instance : Algebra ((p.heightOneSpectrum.adicCompletion K)) ((q.1.heightOneSpectrum.adicCompletion L)) :=
  (completionMap p q).toAlgebra

scoped instance : IsScalarTower K ((p.heightOneSpectrum.adicCompletion K)) ((q.1.heightOneSpectrum.adicCompletion L)) :=
  .of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, completionMap_algebraMap]
    exact IsScalarTower.algebraMap_apply K L ((q.1.heightOneSpectrum.adicCompletion L)) x

scoped instance : ContinuousSMul ((p.heightOneSpectrum.adicCompletion K)) ((q.1.heightOneSpectrum.adicCompletion L)) where
  continuous_smul :=
    ((continuous_completionMap p q).comp continuous_fst).mul continuous_snd

/-- The canonical tensor map to this actual upper completion. -/
def tensorMap :
    (p.heightOneSpectrum.adicCompletion K) ⊗[K] L →ₐ[(p.heightOneSpectrum.adicCompletion K)] (q.1.heightOneSpectrum.adicCompletion L) :=
  Algebra.TensorProduct.lift (Algebra.algHom _ _ _) (Algebra.algHom _ _ _)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorMap_tmul (a : (p.heightOneSpectrum.adicCompletion K)) (x : L) :
    tensorMap p q (a ⊗ₜ[K] x) =
      completionMap p q a * algebraMap L ((q.1.heightOneSpectrum.adicCompletion L)) x := rfl

theorem tensorMap_denseRange : DenseRange (tensorMap p q) := by
  apply (q.1.heightOneSpectrum.denseRange_algebraMap L).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨1 ⊗ₜ[K] x, by simp⟩

variable [FiniteDimensional K L]

/-- Density and closedness of finite-dimensional subspaces prove surjectivity. -/
theorem tensorMap_surjective : Function.Surjective (tensorMap p q) := by
  let : (Valued.v : Valuation (p.heightOneSpectrum.adicCompletion K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NontriviallyNormedField (p.heightOneSpectrum.adicCompletion K) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  let f := (tensorMap p q).toLinearMap
  have hc : IsClosed (Set.range (tensorMap p q)) := by
    exact Submodule.closed_of_finiteDimensional
      (𝕜 := p.heightOneSpectrum.adicCompletion K) f.range
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans (tensorMap_denseRange p q).closure_range)

/-- Each actual upper completion is finite over the actual lower completion. -/
scoped instance localFinite :
    Module.Finite ((p.heightOneSpectrum.adicCompletion K)) ((q.1.heightOneSpectrum.adicCompletion L)) :=
  Module.Finite.of_surjective (tensorMap p q).toLinearMap (tensorMap_surjective p q)

end CurvePlaceCompletionExtension

variable [IsScalarTower k K L] [FiniteDimensional K L]

/-- Every actual lower curve place has an actual upper curve place. -/
instance curvePlacesAbove_nonempty (p : AlgebraicCurve.Place k K) :
    Nonempty (CurvePlacesAbove k L p) :=
  ⟨⟨curvePlaceExtension (F := L) p, curvePlaceExtension_comap p⟩⟩

end Langlands.Global
