import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

noncomputable section

namespace Langlands.Global.AdelicFunctoriality.FiniteExtension

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension Valued WithZero
open WithZeroTopology

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver p.asIdeal]

theorem valuation_completionMap (x : p.adicCompletion K) :
    (Valued.v (completionMap p q x) : ℤᵐ⁰) =
      Valued.v x ^ q.asIdeal.ramificationIdx (𝓞 K) := by
  have hp := Valued.continuous_valuation_of_surjective (p.valuedAdicCompletion_surjective K)
  have hq := Valued.continuous_valuation_of_surjective (q.valuedAdicCompletion_surjective L)
  refine congrFun ((p.denseRange_algebraMap K).equalizer
    (hq.comp (continuous_completionMap p q)) (hp.pow _) ?_) x
  funext a
  change Valued.v (completionMap p q (algebraMap K (p.adicCompletion K) a)) =
    Valued.v (algebraMap K (p.adicCompletion K) a) ^ q.asIdeal.ramificationIdx (𝓞 K)
  rw [completionMap_coe]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, valuedAdicCompletion_eq_valuation']
  rw [← valuation_liesOver L p q,
    Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal q.asIdeal p.ne_bot]

theorem completionMap_mem_integers_iff (x : p.adicCompletion K) :
    completionMap p q x ∈ q.adicCompletionIntegers L ↔ x ∈ p.adicCompletionIntegers K := by
  change Valued.v (completionMap p q x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [valuation_completionMap]
  exact pow_le_one_iff_of_nonneg zero_le (q.asIdeal.ramificationIdx_pos (𝓞 K)).ne'

/-- The canonical completion embedding restricted to the actual integral rings. -/
def completionIntegersMap : p.adicCompletionIntegers K →+* q.adicCompletionIntegers L :=
  (completionMap p q).restrict (p.adicCompletionIntegers K).toSubring
    (q.adicCompletionIntegers L).toSubring (fun x hx =>
      (completionMap_mem_integers_iff p q x).mpr hx)

@[simp] theorem completionIntegersMap_coe (x : p.adicCompletionIntegers K) :
    (completionIntegersMap p q x : q.adicCompletion L) = completionMap p q x := rfl

scoped instance : Algebra (p.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
  (completionIntegersMap p q).toAlgebra

scoped instance : IsScalarTower (p.adicCompletionIntegers K)
    (p.adicCompletion K) (q.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (p.adicCompletionIntegers K)
    (q.adicCompletionIntegers L) (q.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsLocalHom (algebraMap (p.adicCompletionIntegers K)
    (q.adicCompletionIntegers L)) where
  map_nonunit x hx := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one] at hx ⊢
    change Valued.v (completionMap p q x) = 1 at hx
    rw [valuation_completionMap] at hx
    exact (pow_eq_one_iff_of_nonneg zero_le
      (q.asIdeal.ramificationIdx_pos (𝓞 K)).ne').mp hx

theorem completionIntegers_intValuation (x : p.adicCompletionIntegers K) :
    (IsDiscreteValuationRing.maximalIdeal (p.adicCompletionIntegers K)).intValuation x =
      (Valued.v (x : p.adicCompletion K) : ℤᵐ⁰) := by
  let R := p.adicCompletionIntegers K
  let m := IsDiscreteValuationRing.maximalIdeal R
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hπv : Valued.v (π : p.adicCompletion K) = WithZero.exp (-1) := by
    have h := Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (Valued.v : Valuation (p.adicCompletion K) ℤᵐ⁰)) hπ.maximalIdeal_eq
    exact h.trans (congrArg (fun a : ℤᵐ⁰ˣ => (a : ℤᵐ⁰))
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (p.valuedAdicCompletion_surjective K)))
  have hπm : m.intValuation π = WithZero.exp (-1) :=
    m.intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
  have hu : m.intValuation (u : R) = 1 := by simp [m, IsDiscreteValuationRing.maximalIdeal]
  have huv : Valued.v ((u : R) : p.adicCompletion K) = 1 :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mp u.isUnit
  change m.intValuation ((u : R) * π ^ n) =
    Valued.v (((u : R) : p.adicCompletion K) * (π : p.adicCompletion K) ^ n)
  rw [map_mul, map_pow, map_mul, map_pow, hu, huv, hπv, hπm]

scoped instance : Module.IsTorsionFree (p.adicCompletionIntegers K)
    (q.adicCompletionIntegers L) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr fun _x _y h =>
    Subtype.ext ((completionMap p q).injective (congrArg Subtype.val h))

theorem completionIntegers_ramificationIdx :
    (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).ramificationIdx
      (p.adicCompletionIntegers K) = q.asIdeal.ramificationIdx (𝓞 K) := by
  let m := IsDiscreteValuationRing.maximalIdeal (p.adicCompletionIntegers K)
  let n := IsDiscreteValuationRing.maximalIdeal (q.adicCompletionIntegers L)
  have : n.asIdeal.LiesOver m.asIdeal :=
    inferInstanceAs ((IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).LiesOver
      (IsLocalRing.maximalIdeal (p.adicCompletionIntegers K)))
  obtain ⟨π, hπ⟩ := m.intValuation_exists_uniformizer
  have h := intValuation_liesOver m n π
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ m.ne_bot] at h
  change m.intValuation π ^
    (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).ramificationIdx
      (p.adicCompletionIntegers K) = n.intValuation (completionIntegersMap p q π) at h
  rw [hπ] at h
  rw [completionIntegers_intValuation q, completionIntegersMap_coe,
    valuation_completionMap, ← completionIntegers_intValuation p, hπ] at h
  exact pow_right_injective₀ (by simp) (by simp [← WithZero.exp_zero]) h

end Langlands.Global.AdelicFunctoriality.FiniteExtension
