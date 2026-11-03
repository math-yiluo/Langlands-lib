import Langlands.HarmonicAnalysis.CanonicalConductorDepthStatement
import Langlands.LocalField.Normalization.Proof
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Topology Filter

universe u

namespace Langlands.HarmonicAnalysis

private theorem principalUnitNeighborhood
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (n : ℕ) :
    ∃ s : Set F.Carrier, s ∈ @nhds F.Carrier T.topology 1 ∧
      ∀ x : F.Carrierˣ, (x : F.Carrier) ∈ s → x ∈ T.principalUnits n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hO : IsOpen (T.Integers : Set F.Carrier) :=
    (ValuativeRel.valuation F.Carrier).isOpen_integer
  let s : Set F.Carrier :=
    {x | x ∈ T.Integers ∧ x⁻¹ ∈ T.Integers ∧
      (x - 1) / T.uniformizer ^ (n : ℤ) ∈ T.Integers}
  refine ⟨s, ?_, ?_⟩
  · have h1 : (T.Integers : Set F.Carrier) ∈ 𝓝 (1 : F.Carrier) :=
      hO.mem_nhds T.Integers.one_mem
    have hi : {x : F.Carrier | x⁻¹ ∈ T.Integers} ∈ 𝓝 (1 : F.Carrier) :=
      (continuousAt_inv₀ one_ne_zero).preimage_mem_nhds (by simpa using h1)
    have hd : {x : F.Carrier | (x - 1) / T.uniformizer ^ (n : ℤ) ∈ T.Integers} ∈
        𝓝 (1 : F.Carrier) :=
      ((continuousAt_id.sub continuousAt_const).div_const _).preimage_mem_nhds
        (by simpa using hO.mem_nhds T.Integers.zero_mem)
    exact inter_mem h1 (inter_mem hi hd)
  · intro x hx
    rw [T.mem_principalUnits_iff_div_mem_integers]
    refine ⟨?_, hx.2.2⟩
    have ha := (T.mem_integers_iff_discreteValuation_le_one _).mp hx.1
    have hb := (T.mem_integers_iff_discreteValuation_le_one _).mp hx.2.1
    have hp : 0 < T.discreteValuation (x : F.Carrier) :=
      pos_iff_ne_zero.mpr ((map_ne_zero T.discreteValuation).mpr x.ne_zero)
    apply le_antisymm ha
    apply (inv_le_one₀ hp).mp
    simpa using hb

private theorem canonicalPrincipalUnitDepth
    : CanonicalPrincipalUnitDepthStatement.{u} := by
  intro p hp F T n
  obtain ⟨s, hs, hsub⟩ := principalUnitNeighborhood F T n
  rw [T.topology_eq_canonicalNormTopology] at hs
  let := F.canonicalNormedField
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  have hp1 : 1 < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨k, fun x hx => hsub x (hεs ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm]
  apply lt_trans hx
  simpa only [zpow_neg, zpow_natCast, inv_pow] using hk

private theorem canonicalBall_mem_nhds
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (s : ℕ) :
    letI := T.topology
    {x : F.Carrierˣ |
      F.canonicalNorm ((x : F.Carrier) - 1) < (p : ℝ) ^ (-(s : ℤ))} ∈ 𝓝 1 := by
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  apply (isOpen_lt ((Units.continuous_val.sub continuous_const).norm)
    continuous_const).mem_nhds
  change ‖(1 : F.Carrier) - 1‖ < (p : ℝ) ^ (-(s : ℤ))
  simp only [sub_self, norm_zero]
  exact zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _

private theorem canonicalCharacterDepth
    (hdepth : CanonicalPrincipalUnitDepthStatement.{u}) :
    CanonicalCharacterDepthStatement.{u} := by
  intro p hp F T
  let := T.topology
  intro P
  constructor
  · intro h r
    obtain ⟨s, hs⟩ := hdepth p F T r
    obtain ⟨χ, hP, x, hx, hχ⟩ := h s
    refine ⟨χ, hP, ?_⟩
    have hlt : r < T.multiplicativeConductor χ := by
      by_contra! hle
      exact hχ ((T.multiplicativeTrivialAt_iff_conductor_le χ r).mpr hle x (hs x hx))
    exact hlt.le
  · intro h s
    let U : Set F.Carrierˣ :=
      {x | F.canonicalNorm ((x : F.Carrier) - 1) < (p : ℝ) ^ (-(s : ℤ))}
    have hU : U ∈ 𝓝 (1 : F.Carrierˣ) := canonicalBall_mem_nhds F T s
    obtain ⟨n, hn⟩ := T.exists_principalUnits_subset hU
    obtain ⟨χ, hP, hχ⟩ := h (n + 1)
    obtain ⟨x, hx, hne⟩ :=
      T.exists_nontrivial_below_multiplicativeConductor χ n (by omega)
    exact ⟨χ, hP, x, hn hx, hne⟩

/-- Canonical norm depth and the Library multiplicative conductor define
the same unbounded character families, retaining all additional conditions. -/
theorem canonicalConductorDepth : CanonicalConductorDepthStatement.{u} :=
  ⟨canonicalPrincipalUnitDepth, canonicalCharacterDepth canonicalPrincipalUnitDepth⟩

end Langlands.HarmonicAnalysis
