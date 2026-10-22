import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! # Actual extensions of completed number fields and their local norms -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

private theorem continuous_fieldNorm
    {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [Algebra F E] [ContinuousSMul F E] [Module.Finite F E] :
    Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h := (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  have heq : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det :=
    funext (Algebra.norm_eq_matrix_det b)
  rw [heq]
  exact h.matrix_det

private theorem continuous_norm_preserves_unitBall
    {E F : Type*} [NontriviallyNormedField E] [NormedField F]
    (f : E →* F) (hf : Continuous f) (hzero : f 0 = 0)
    {x : E} (hx : ‖x‖ ≤ 1) : ‖f x‖ ≤ 1 := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    Metric.continuousAt_iff.mp (hf.continuousAt (x := 0)) 1 zero_lt_one
  obtain ⟨y, hy0, hyδ⟩ := NormedField.exists_norm_lt E hδ
  have hy : y ≠ 0 := norm_pos_iff.mp hy0
  have hfy : 0 < ‖f y‖ := norm_pos_iff.mpr (by
    intro h
    have hmul := map_mul f y y⁻¹
    rw [mul_inv_cancel₀ hy, map_one, h, zero_mul] at hmul
    exact one_ne_zero hmul)
  by_contra! hgt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ‖f y‖) hgt
  have hinput : dist (y * x ^ n) 0 < δ := by
    rw [dist_zero_right, norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)).trans_lt hyδ
  have hout := hsmall hinput
  rw [hzero, dist_zero_right, map_mul, map_pow, norm_mul, norm_pow] at hout
  have hlarge : 1 < ‖f y‖ * ‖f x‖ ^ n := by
    exact (div_lt_iff₀ hfy).mp hn |>.trans_eq (mul_comm _ _)
  exact (lt_asymm hout hlarge)

namespace FiniteExtension

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Valued

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver p.asIdeal]

/-- The completion embedding induced by the field embedding at an actual prime above `p`. -/
def completionMap : p.adicCompletion K →+* q.adicCompletion L :=
  ((adicCompletion.equiv L q).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (p.valuation K)) (WithVal (q.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L p q).continuous)).comp
    (adicCompletion.equiv K p).toRingHom

theorem continuous_completionMap : Continuous (completionMap p q) :=
  (adicCompletion.continuous_ofCompletion L q).comp
    (UniformSpace.Completion.continuous_map.comp
      (adicCompletion.continuous_toCompletion K p))

@[simp] theorem completionMap_coe (x : K) :
    completionMap p q (algebraMap K (p.adicCompletion K) x) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
  apply (adicCompletion.equiv L q).injective
  change UniformSpace.Completion.mapRingHom
    (algebraMap (WithVal (p.valuation K)) (WithVal (q.valuation L)))
    (uniformContinuous_algebraMap_liesOver K L p q).continuous
    (↑(WithVal.toVal (p.valuation K) x)) = _
  exact UniformSpace.Completion.mapRingHom_coe
    (f := algebraMap (WithVal (p.valuation K)) (WithVal (q.valuation L)))
    (uniformContinuous_algebraMap_liesOver K L p q).continuous _

/-- The local algebra is constructed from the continuous completion embedding. -/
scoped instance : Algebra (p.adicCompletion K) (q.adicCompletion L) :=
  (completionMap p q).toAlgebra

scoped instance : IsScalarTower K (p.adicCompletion K) (q.adicCompletion L) :=
  .of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, completionMap_coe]
    exact IsScalarTower.algebraMap_apply K L (q.adicCompletion L) x

scoped instance : ContinuousSMul (p.adicCompletion K) (q.adicCompletion L) where
  continuous_smul := ((continuous_completionMap p q).comp continuous_fst).mul continuous_snd

/-- This is the determinant norm of the constructed finite extension of completed fields. -/
def localNorm : q.adicCompletion L →* p.adicCompletion K :=
  Algebra.norm (p.adicCompletion K)

theorem local_finite : Module.Finite (p.adicCompletion K) (q.adicCompletion L) :=
  inferInstance

@[simp] theorem localNorm_algebraMap (x : p.adicCompletion K) :
    localNorm p q (completionMap p q x) =
      x ^ Module.finrank (p.adicCompletion K) (q.adicCompletion L) :=
  Algebra.norm_algebraMap _

theorem continuous_localNorm : Continuous (localNorm p q) := by
  change Continuous (Algebra.norm (p.adicCompletion K) : q.adicCompletion L → p.adicCompletion K)
  exact continuous_fieldNorm

/-- The actual local norm carries the completed integral subring into the base one. -/
theorem localNorm_integral {x : q.adicCompletion L} (hx : x ∈ q.adicCompletionIntegers L) :
    localNorm p q x ∈ p.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
  apply continuous_norm_preserves_unitBall (localNorm p q) (continuous_localNorm p q)
    Algebra.norm_zero
  exact Valued.toNormedField.norm_le_one_iff.mpr hx

/-- Continuous local norm on the actual local unit groups. -/
def localUnitNorm : (q.adicCompletion L)ˣ →ₜ* (p.adicCompletion K)ˣ where
  __ := Units.map (localNorm p q)
  continuous_toFun := (continuous_localNorm p q).units_map

@[simp] theorem localUnitNorm_val (x : (q.adicCompletion L)ˣ) :
    (localUnitNorm p q x : p.adicCompletion K) = localNorm p q x := rfl

theorem localUnitNorm_integral {x : (q.adicCompletion L)ˣ}
    (hx : x ∈ (q.adicCompletionIntegers L).units) :
    localUnitNorm p q x ∈ (p.adicCompletionIntegers K).units := by
  rcases hx with ⟨hx, hxi⟩
  exact ⟨localNorm_integral p q hx, localNorm_integral p q hxi⟩

end FiniteExtension

namespace InfiniteExtension

open NumberField
open scoped NumberField.LiesOver

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra K L]
  (p : InfinitePlace K) (q : InfinitePlace L) [q.LiesOver p]

local instance : NontriviallyNormedField p.Completion :=
  { (inferInstance : NormedField p.Completion) with
    non_trivial := by
      refine ⟨2, ?_⟩
      have h := (InfinitePlace.Completion.isometry_extensionEmbedding p).norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.extensionEmbedding p)) (2 : p.Completion)
      rw [← h]
      norm_num only [map_ofNat, Complex.norm_ofNat] }

scoped instance : Module.Finite p.Completion q.Completion := by
  apply Module.finite_of_finrank_pos
  rcases q.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one p]
    exact Nat.zero_lt_one
  · rw [h.finrank_eq_two p]
    exact Nat.zero_lt_two

/-- The determinant norm of the actual extension at infinite places. -/
def localNorm : q.Completion →* p.Completion :=
  Algebra.norm p.Completion

theorem local_finite : Module.Finite p.Completion q.Completion := inferInstance

theorem continuous_localNorm : Continuous (localNorm p q) := by
  change Continuous (Algebra.norm p.Completion : q.Completion → p.Completion)
  exact continuous_fieldNorm (F := p.Completion) (E := q.Completion)

@[simp] theorem localNorm_algebraMap (x : p.Completion) :
    localNorm p q (NumberField.LiesOver.completionMap x) =
      x ^ Module.finrank p.Completion q.Completion :=
  Algebra.norm_algebraMap _

/-- The continuous norm on units at an infinite place. -/
def localUnitNorm : q.Completionˣ →ₜ* p.Completionˣ where
  __ := Units.map (localNorm p q)
  continuous_toFun := (continuous_localNorm p q).units_map

@[simp] theorem localUnitNorm_val (x : q.Completionˣ) :
    (localUnitNorm p q x : p.Completion) = localNorm p q x := rfl

end InfiniteExtension
end Langlands.Global.AdelicFunctoriality
