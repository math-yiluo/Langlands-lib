/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper

Modified by Worker 461 (2026): adapt the integral-range and BijOn arguments of
Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/Completion/BaseChange.lean:364-547 and :854-870.
Adapt the Chinese remainder and product-closure arguments from
FLT/DedekindDomain/AdicValuation.lean:331-403 at the same commit.
Use the Library's canonical maps and finite-place index. Replace the open lattice
argument by compactness of a finite coefficient space over the completed integers.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.IntegralTensorTransportProof
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdeleQuotientCompactProof
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct FiniteExtension WithZero

universe u v

variable {K : Type u} (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

private theorem comparison_bijective (p : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (integralTensorComparison L p) := by
  have h := ((completedTensorComparison K L).1 p).comp
    (integralTensorTransportBijective K L p)
  simpa only [Function.comp_def, finiteTensorMap_integralTensorTransport] using h

private theorem integral_image_subset (p : HeightOneSpectrum (𝓞 K)) :
    Set.range (integralTensorComparison L p ∘ integralTensorInclusion L p) ⊆
      Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) := by
  rintro _ ⟨z, rfl⟩
  intro q _
  induction z with
  | tmul b x =>
    rw [Function.comp_apply, integralTensorComparison_integralTensorInclusion_tmul]
    exact mul_mem (coe_mem_adicCompletionIntegers q.1 b)
      (FiniteExtension.completionIntegersMap p q.1 x).property
  | add z w hz hw =>
    change integralTensorComparison L p (integralTensorInclusion L p (z + w)) q ∈
      q.1.adicCompletionIntegers L
    rw [map_add, map_add, Pi.add_apply]
    exact (q.1.adicCompletionIntegers L).add_mem _ _ hz hw

omit [NumberField L] in
private theorem tensor_coefficients {n : ℕ} (b : Fin n → 𝓞 L)
    (hb : Submodule.span (𝓞 K) (Set.range b) = ⊤)
    (p : HeightOneSpectrum (𝓞 K))
    (z : 𝓞 L ⊗[𝓞 K] p.adicCompletionIntegers K) :
    ∃ x : Fin n → p.adicCompletionIntegers K, ∑ i, b i ⊗ₜ[𝓞 K] x i = z := by
  classical
  induction z with
  | tmul a y =>
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp
      (show a ∈ Submodule.span (𝓞 K) (Set.range b) by rw [hb]; trivial)
    refine ⟨fun i => c i • y, ?_⟩
    rw [← hc, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.tmul_smul _ _ _
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, by simp only [Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

private theorem integral_image_closed (p : HeightOneSpectrum (𝓞 K)) :
    IsClosed (Set.range (integralTensorComparison L p ∘ integralTensorInclusion L p)) := by
  classical
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := 𝓞 K) (M := 𝓞 L)
  let f : (Fin n → p.adicCompletionIntegers K) →
      ((q : FinitePlacesAbove L p) → q.1.adicCompletion L) :=
    fun x q => ∑ i, algebraMap (𝓞 L) (q.1.adicCompletion L) (b i) *
      FiniteExtension.completionMap p q.1 (x i)
  have hf : Continuous f := by
    apply continuous_pi
    intro q
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((FiniteExtension.continuous_completionMap p q.1).comp
        (continuous_subtype_val.comp (continuous_apply i)))
  have hr : Set.range f =
      Set.range (integralTensorComparison L p ∘ integralTensorInclusion L p) := by
    have he (x : Fin n → p.adicCompletionIntegers K) :
        f x = integralTensorComparison L p
          (integralTensorInclusion L p (∑ i, b i ⊗ₜ[𝓞 K] x i)) := by
      ext q
      simp only [map_sum, Finset.sum_apply,
        integralTensorComparison_integralTensorInclusion_tmul,
        FiniteExtension.completionIntegersMap_coe, f]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨∑ i, b i ⊗ₜ[𝓞 K] x i, (he x).symm⟩
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := tensor_coefficients L b hb p z
      exact ⟨x, he x⟩
  let : CompactSpace (p.adicCompletionIntegers K) :=
    isCompact_iff_compactSpace.mp (Langlands.Global.isCompact_adicCompletionIntegers K p)
  rw [← hr]
  exact (isCompact_range hf).isClosed

private theorem integer_approximation (q : HeightOneSpectrum (𝓞 L))
    (x : q.adicCompletionIntegers L) {ε : ℤᵐ⁰} (hε : ε ≠ 0) :
    ∃ a : 𝓞 L, Valued.v (x.val - algebraMap (𝓞 L) (q.adicCompletion L) a) < ε := by
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt hε
  obtain ⟨π, hπ⟩ := q.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    intro h
    exact WithZero.exp_ne_zero (hπ.symm.trans (by simp [h]))
  obtain ⟨a, ha⟩ := Langlands.Global.exists_integer_sub_valued_le q x.property
    (pow_ne_zero n hπ0)
  refine ⟨a, ha.trans_lt ?_⟩
  rw [Langlands.Global.valued_algebraMap_integer, map_pow, hπ]
  simpa only [← WithZero.exp_nsmul, smul_neg, nsmul_one] using hn

omit [NumberField K] in
private theorem simultaneous_integer_approximation (p : HeightOneSpectrum (𝓞 K))
    (s : Finset (FinitePlacesAbove L p))
    (ε : FinitePlacesAbove L p → ℤᵐ⁰) (hε : ∀ q, ε q ≠ 0)
    (x : (q : FinitePlacesAbove L p) → q.1.adicCompletionIntegers L) :
    ∃ a : 𝓞 L, ∀ q ∈ s,
      Valued.v ((algebraMap (𝓞 L) (q.1.adicCompletion L) a) - (x q).val) < ε q := by
  classical
  choose b hb using fun q => integer_approximation L q.1 (x q) (hε q)
  choose n hn using fun q => WithZero.exists_exp_neg_natCast_lt (hε q)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun q : FinitePlacesAbove L p => q.1.asIdeal) n
    (fun q _ => q.1.prime)
    (fun q _ r _ hqr e => hqr (Subtype.ext (HeightOneSpectrum.ext e))) (fun q => b q.1)
  refine ⟨a, fun q hq => ?_⟩
  have hsub : Valued.v (algebraMap (𝓞 L) (q.1.adicCompletion L) (a - b q)) < ε q := by
    rw [Langlands.Global.valued_algebraMap_integer]
    exact ((intValuation_le_pow_iff_mem q.1 _ _).mpr (ha q hq)).trans_lt (hn q)
  have hx := hb q
  rw [Valuation.map_sub_swap] at hx
  calc
    Valued.v (algebraMap (𝓞 L) (q.1.adicCompletion L) a - (x q).val) =
        Valued.v (algebraMap (𝓞 L) (q.1.adicCompletion L) (a - b q) +
          (algebraMap (𝓞 L) (q.1.adicCompletion L) (b q) - (x q).val)) := by
      rw [map_sub (algebraMap (𝓞 L) (q.1.adicCompletion L)), sub_add_sub_cancel]
    _ < ε q := Valuation.map_add_lt _ hsub hx

omit [NumberField K] in
private theorem integral_product_subset_closure (p : HeightOneSpectrum (𝓞 K)) :
    Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) ⊆
      closure (Set.range (algebraMap (𝓞 L)
        ((q : FinitePlacesAbove L p) → q.1.adicCompletion L))) := by
  classical
  intro x hx
  rw [mem_closure_iff_nhds_zero]
  intro U hU
  rw [Pi.zero_def, nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨s, t, ht, hsub⟩ := hU
  choose γ hγ using fun q : FinitePlacesAbove L p =>
    (Valued.is_topological_valuation (t q)).mp (ht q)
  choose y hy using fun q : FinitePlacesAbove L p =>
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation (q.1.adicCompletion L) ℤᵐ⁰)) (γ q).val
  have hy0 (q) : Valued.v (y q) ≠ 0 := by
    have h : y q ≠ 0 := by
      intro h
      exact (γ q).ne_zero (by simpa [h] using (hy q).symm)
    simpa using h
  obtain ⟨a, ha⟩ := simultaneous_integer_approximation L p s
    (fun q => Valued.v (y q)) hy0 (fun q => ⟨x q, hx q trivial⟩)
  refine ⟨algebraMap (𝓞 L) _ a, Set.mem_range_self a, hsub ?_⟩
  intro q hq
  apply hγ q
  change Valued.v.restrict _ < (γ q).val
  rw [← hy q]
  change Valued.v.restrict _ < Valued.v.restrict (y q)
  rw [Valuation.restrict_lt_iff]
  exact ha q hq

private theorem integral_image_eq (p : HeightOneSpectrum (𝓞 K)) :
    Set.range (integralTensorComparison L p ∘ integralTensorInclusion L p) =
      Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) := by
  apply Set.Subset.antisymm (integral_image_subset L p)
  refine (integral_product_subset_closure L p).trans ?_
  apply closure_minimal _ (integral_image_closed L p)
  rintro _ ⟨b, rfl⟩
  refine ⟨b ⊗ₜ[𝓞 K] (1 : p.adicCompletionIntegers K), ?_⟩
  funext q
  change integralTensorComparison L p
    (integralTensorInclusion L p (b ⊗ₜ[𝓞 K] (1 : p.adicCompletionIntegers K))) q =
      algebraMap (𝓞 L) (q.1.adicCompletion L) b
  rw [integralTensorComparison_integralTensorInclusion_tmul]
  simp only [map_one, OneMemClass.coe_one, mul_one]

/-- The canonical integral local tensor comparison is bijective and carries the actual
integral inclusion range exactly onto the product of the local integer rings. -/
theorem integralLocalTensorComparison : IntegralLocalTensorComparison.{u, v} := by
  intro K L _ _ _ _ _ p
  have hb := comparison_bijective L p
  have hr := integral_image_eq L p
  refine ⟨hb, hr, ?_, hb.1.injOn, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [← hr]
    exact ⟨z, rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨integralTensorInclusion L p z, ⟨z, rfl⟩, rfl⟩

end Langlands.Global.AdelicFunctoriality
