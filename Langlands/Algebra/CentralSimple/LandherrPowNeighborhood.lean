import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Algebra.Group.Basic

/-! # Powers near one in complete fields and a continuity lemma for quotients -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Filter Topology

/-- Over a complete nontrivially normed field of characteristic zero, for `n ≠ 0`
every element sufficiently close to `1` is an `n`-th power of a nonzero element. -/
theorem powSet_mem_nhds {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    {n : ℕ} (hn : n ≠ 0) : {x : K | ∃ s : K, s ≠ 0 ∧ s ^ n = x} ∈ 𝓝 (1 : K) := by
  have hderiv : HasStrictDerivAt (fun x : K => x ^ n) ((n : K) * 1 ^ (n - 1)) 1 :=
    hasStrictDerivAt_pow n 1
  have hne : (n : K) * 1 ^ (n - 1) ≠ 0 := by simpa using hn
  have hmap : map (fun x : K => x ^ n) (𝓝 1) = 𝓝 1 := by
    simpa using hderiv.map_nhds_eq hne
  have himage : (fun x : K => x ^ n) '' {x : K | x ≠ 0} ∈ 𝓝 (1 : K) := by
    rw [← hmap]
    exact image_mem_map (isOpen_ne.mem_nhds one_ne_zero)
  refine mem_of_superset himage ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, hs, rfl⟩

/-- For a continuous map `φ` into a normed field, the quotient
`κ (φ P + ρ φ Q) / (φ P - ρ φ Q)` takes values in any given neighbourhood of `1` for `(P, Q)`
sufficiently near a point where the denominator is nonzero and the quotient is `1`. -/
theorem ratio_preimage_mem_nhds {k K : Type*} [TopologicalSpace k] [NormedField K]
    (φ : k → K) (hφ : Continuous φ) (ρ κ : K) (P₀ Q₀ : k) (hD : φ P₀ - ρ * φ Q₀ ≠ 0)
    (h1 : κ * (φ P₀ + ρ * φ Q₀) / (φ P₀ - ρ * φ Q₀) = 1) {U : Set K} (hU : U ∈ 𝓝 1) :
    {PQ : k × k | κ * (φ PQ.1 + ρ * φ PQ.2) / (φ PQ.1 - ρ * φ PQ.2) ∈ U} ∈ 𝓝 (P₀, Q₀) := by
  have h1' : (φ ∘ Prod.fst : k × k → K) = fun PQ => φ PQ.1 := rfl
  have hc1 : Continuous fun PQ : k × k => φ PQ.1 := hφ.comp continuous_fst
  have hc2 : Continuous fun PQ : k × k => φ PQ.2 := hφ.comp continuous_snd
  have hcont : ContinuousAt
      (fun PQ : k × k => κ * (φ PQ.1 + ρ * φ PQ.2) / (φ PQ.1 - ρ * φ PQ.2)) (P₀, Q₀) := by
    apply ContinuousAt.div
    · exact (continuous_const.mul (hc1.add (continuous_const.mul hc2))).continuousAt
    · exact (hc1.sub (continuous_const.mul hc2)).continuousAt
    · exact hD
  exact hcont.preimage_mem_nhds (by simpa only [h1] using hU)

end Langlands.CentralSimple.Landherr
