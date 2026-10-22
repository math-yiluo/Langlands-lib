import Langlands.Global.AdelicFunctoriality.Extension
import Langlands.LocalField.CanonicalProof
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Finite completions of number fields as p-adic fields

For a finite place `v` of a number field `K`, the completion `v.adicCompletion K`
is packaged as a `PadicField` over `ℚ_p`, where `p` is the rational prime below `v`.
The `ℚ_p`-algebra structure is the continuous completion of the inclusion `ℚ → K`.
`topologicalData v` keeps the completion's own topology; its valuative relation is
proved to be that of the completion's valuation, and its integral elements are the
completed integers.

Sources: Serre, *Local Fields* (1979), Chapter II, Sections 2-3, pages 28-31.
See the paired Markdown for the construction and the proof route.
-/

noncomputable section

namespace Langlands.Global.CompletionPadic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped NumberField WithZero Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The finite place of `ℚ` below `v`. -/
abbrev rationalPlace : HeightOneSpectrum (𝓞 ℚ) := v.under (𝓞 ℚ)

instance liesOver_rationalPlace : v.asIdeal.LiesOver (rationalPlace v).asIdeal :=
  Ideal.over_under v.asIdeal

/-- The residue characteristic of `v`. -/
abbrev residuePrime : ℕ := Rat.HeightOneSpectrum.primesEquiv (rationalPlace v)

instance residuePrime_fact : Fact (residuePrime v).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv (rationalPlace v)).2⟩

/-- The continuous ring embedding `ℚ_p → K_v`. -/
def padicMap : Padic (residuePrime v) →+* v.adicCompletion K :=
  (AdelicFunctoriality.FiniteExtension.completionMap (rationalPlace v) v).comp
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)).symm.toRingEquiv.toRingHom

theorem continuous_padicMap : Continuous (padicMap v) :=
  (AdelicFunctoriality.FiniteExtension.continuous_completionMap (rationalPlace v) v).comp
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)).symm.continuous

/-- The `ℚ_p`-algebra structure on `K_v`. -/
@[instance_reducible]
def padicAlgebra : Algebra (Padic (residuePrime v)) (v.adicCompletion K) :=
  (padicMap v).toAlgebra

theorem padicFinite :
    letI := padicAlgebra v
    FiniteDimensional (Padic (residuePrime v)) (v.adicCompletion K) := by
  let := padicAlgebra v
  have := AdelicFunctoriality.FiniteExtension.local_finite (rationalPlace v) v
  refine Module.Finite.of_equiv_equiv
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)).toRingEquiv
    (RingEquiv.refl _) ?_
  refine RingHom.ext fun x => ?_
  change AdelicFunctoriality.FiniteExtension.completionMap (rationalPlace v) v
      ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)).symm
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v) x)) =
    AdelicFunctoriality.FiniteExtension.completionMap (rationalPlace v) v x
  rw [ContinuousAlgEquiv.symm_apply_apply]

/-- `K_v` as a finite extension of `ℚ_p`. -/
abbrev padicField : PadicField.{u} (residuePrime v) where
  Carrier := v.adicCompletion K
  algebra := padicAlgebra v
  finiteDimensional := padicFinite v

/-- The completion topology is the `ℚ_p`-module topology. -/
theorem completion_isModuleTopology :
    letI := padicAlgebra v
    IsModuleTopology (Padic (residuePrime v)) (v.adicCompletion K) := by
  let := padicAlgebra v
  have := padicFinite v
  have : ContinuousSMul (Padic (residuePrime v)) (v.adicCompletion K) :=
    continuousSMul_of_algebraMap _ _ (continuous_padicMap v)
  exact isModuleTopologyOfFiniteDimensional

/-- The completion topology equals the canonical topology of the `PadicField`. -/
theorem completion_topology_eq :
    inferInstanceAs (TopologicalSpace (v.adicCompletion K)) =
      (padicField v).canonicalTopologicalData.topology := by
  rw [PadicField.canonicalTopologicalData_topology]
  let := padicAlgebra v
  have := completion_isModuleTopology v
  exact eq_moduleTopology (Padic (residuePrime v)) (v.adicCompletion K)

theorem norm_lt_one_iff_tendsto_pow {E : Type*} [NormedField E] (x : E) :
    ‖x‖ < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.symm

/-- Both absolute values detect the same elements of absolute value less than one. -/
theorem valued_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ (padicField v).canonicalNorm x < 1 := by
  have h₁ : Valued.v x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
    Valued.toNormedField.norm_lt_one_iff.symm.trans
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.symm
  have h₂ : (padicField v).canonicalNorm x < 1 ↔
      Tendsto (fun n : ℕ => x ^ n) atTop
        (@nhds _ (padicField v).canonicalTopologicalData.topology 0) :=
    @norm_lt_one_iff_tendsto_pow _ (padicField v).canonicalNormedField.toNormedField x
  rw [← completion_topology_eq v] at h₂
  exact h₁.trans h₂.symm

/-- The valuation of the completion and the base-extending spectral valuation are equivalent. -/
theorem valued_isEquiv :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsEquiv
      (padicField v).canonicalValuation :=
  Valuation.isEquiv_iff_val_lt_one.mpr fun {x} => (valued_lt_one_iff v x).trans <| by
    rw [← PadicField.canonicalValuation_coe, NNReal.coe_lt_one]

/-- The completed integers are the closed unit ball of the spectral norm. -/
theorem mem_adicCompletionIntegers_iff (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ (padicField v).canonicalNorm x ≤ 1 := by
  rw [mem_adicCompletionIntegers, ← PadicField.canonicalValuation_coe, NNReal.coe_le_one]
  exact (valued_isEquiv v).le_one_iff_le_one

/-- The local-field realization of `K_v` whose topology is the completion topology. -/
def topologicalData : (padicField v).TopologicalData where
  topology := inferInstanceAs (TopologicalSpace (v.adicCompletion K))
  valuativeRel := (padicField v).canonicalTopologicalData.valuativeRel
  valuativeExtension := (padicField v).canonicalTopologicalData.valuativeExtension
  moduleTopology := completion_isModuleTopology v
  localField := by
    have h := (padicField v).canonicalTopologicalData.localField
    rw [← completion_topology_eq v] at h
    exact h

theorem topologicalData_topology :
    (topologicalData v).topology = inferInstanceAs (TopologicalSpace (v.adicCompletion K)) :=
  rfl

/-- The valuative relation of `topologicalData v` is the completion's valuation order. -/
theorem topologicalData_vle (x y : v.adicCompletion K) :
    @ValuativeRel.vle (padicField v).Carrier _ (topologicalData v).valuativeRel x y ↔
      Valued.v x ≤ Valued.v y := by
  refine ((padicField v).canonicalTopologicalData_vle x y).trans ?_
  rw [← PadicField.canonicalValuation_coe,
    ← PadicField.canonicalValuation_coe, NNReal.coe_le_coe]
  exact (valued_isEquiv v x y).symm

end Langlands.Global.CompletionPadic
