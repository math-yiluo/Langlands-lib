import Langlands.Representation.Archimedean.RealCartanPlacementNumerator
import Langlands.Representation.Archimedean.RealCartanSourceDenominator
import Langlands.Representation.Archimedean.RealStandardEllipticCartanScaledTraceReduction

/-! # Elliptic Cartan character comparison of real standard modules -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Langlands.Archimedean.RealStandardEllipticCartan

open Langlands.LocalFactor.Archimedean RealCartanBlockLayout RealCartanFilterSupport
  RealCartanFixedCosets RealCartanPlacedTrace RealCartanPlacementNumerator RealCartanSourceDenominator
  RealCartanTransverseLimit RealInducedStandardBound
  RealLeviCompactChart RealStandardCompactAverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def unshiftedChartCoefficient (ds : List RealBlock) : ℂ :=
  (-1 : ℂ) ^ ds.countP isInducedBlock * (chartCoefficient (blockSizes ds.get) : ℂ)

private theorem unshiftedChartCoefficient_ne_zero (ds : List RealBlock) :
    unshiftedChartCoefficient ds ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.ofReal_ne_zero.mpr
    (chartCoefficient_pos _).ne')

private theorem topLimit_ofFn
    {n r s t : ℕ} (b : Fin t → RealBlock) (hh : (∑ i, blockSizes b i) = n)
    (h : 2 * r + s = n) {x : Coordinates r s} (hx : x ∈ separatedRegularCoordinates r s)
    {d : Fin r → ComplexCharacterData} {a : Fin s → RealCharacterData}
    (hp : (List.ofFn b).Perm (ofBlockData d a)) (hweight : ∀ i, 0 < (d i).weight)
    (q : ℝ) (hq : q ≠ 0) (hden : ∀ (e : Assignment (blockSizes b) (cartanLabel (h.trans hh.symm)))
      (κ : LeviFrame (blockSizes b)), matchedProduct b (h.trans hh.symm) x e κ = q) :
    Tendsto (fun ε => compactLowTrace (compactHaar n) (List.ofFn b) (cartanElement h x)
      (scaledConeTest n ε)) (𝓝[>] (0 : ℝ))
      (𝓝 ((coneMass n : ℂ) * (q : ℂ)⁻¹ * (angularProduct x)⁻¹ *
        ((chartCoefficient (blockSizes b) : ℂ) * numerator (blockParameters d a) x))) := by
  subst n
  have hs := length_slots_ofBlockData (realRank_ofFn b) hp
  have ht := realCartanPlacedTrace t b r s h x hx hs q hq hden
  have ha := angularProduct_ne_zero hx.2
  have he := realCartanPlacementNumerator r s t x b h d a hp hweight
  have hvalue : placementSum b h x = (angularProduct x)⁻¹ * numerator (blockParameters d a) x := by
    rw [← he, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [hvalue] at ht
  convert ht using 2
  ring

set_option maxHeartbeats 550000 in
private theorem scaledTraceLimits_of_placedFormulas :
    RealStandardEllipticCartanScaledTraceLimitsStatement := by
  refine ⟨unshiftedChartCoefficient, unshiftedChartCoefficient_ne_zero, ?_⟩
  intro r s x hx
  obtain ⟨hq, hden⟩ := realCartanSourceDenominator r s x hx
  let q := sourceNormalizedProduct x
  let n := 2 * r + s
  let μ := compactHaar n
  let F := Filter.map (scaledConeTest n) (𝓝[>] (0 : ℝ))
  let c := (coneMass n : ℂ) * (q : ℂ)⁻¹ * (angularProduct x)⁻¹
  have hc : c ≠ 0 := mul_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneMass_pos n).ne')
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hq)))
    (inv_ne_zero (angularProduct_ne_zero hx.2))
  refine ⟨μ, F, c, inferInstance, inferInstance, hc, ?_, ?_⟩
  · intro r' s' ds d a hn hp _ hlt
    change Tendsto _ (Filter.map (scaledConeTest n) (𝓝[>] (0 : ℝ))) _
    rw [Filter.tendsto_map'_iff]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cone_trace (n := n) rfl hx hn hp hlt.le] with ε hε
    exact (hε.2 hlt).symm
  · intro ds d a hn hp hweight
    let b := ds.get
    have hb : List.ofFn b = ds := List.ofFn_get _
    have hh : (∑ i, blockSizes b i) = n := (realRank_ofFn b).symm.trans ((congrArg realRank hb).trans hn)
    have hp' : (List.ofFn b).Perm (ofBlockData d a) := hb.symm ▸ hp
    have hs : ds.countP isInducedBlock = r :=
      (length_slots_eq_count_induced hn).symm.trans (length_slots_ofBlockData hn hp)
    have ht := topLimit_ofFn b hh (rfl : 2 * r + s = n) hx hp' hweight q hq (hden _ _ _)
    have ht' := (tendsto_const_nhds (x := (-1 : ℂ) ^ r)).mul ht
    have hm : (-1 : ℂ) ^ r * (c * ((chartCoefficient (blockSizes b) : ℂ) *
      numerator (blockParameters d a) x)) = c * (unshiftedChartCoefficient ds *
        numerator (blockParameters d a) x) := by
      simp only [unshiftedChartCoefficient, b, hs]
      ring
    change Tendsto _ (Filter.map (scaledConeTest n) (𝓝[>] (0 : ℝ))) _
    rw [Filter.tendsto_map'_iff]
    rw [hb] at ht'
    change Tendsto _ _ (𝓝 ((-1 : ℂ) ^ r * (c * ((chartCoefficient (blockSizes b) : ℂ) *
      numerator (blockParameters d a) x)))) at ht'
    rw [hm] at ht'
    apply ht'.congr'
    filter_upwards [eventually_cone_trace (n := n) rfl hx hn hp le_rfl] with ε hε
    exact hε.1.symm

/-- Isomorphic irreducible real standard modules have common elliptic block counts
and equal Cartan numerators for enumerations of their original block lists. -/
theorem realStandardEllipticCartanComparison : RealStandardEllipticCartanComparisonStatement :=
  realStandardEllipticCartanComparison_of_scaledTraceLimits scaledTraceLimits_of_placedFormulas

end Langlands.Archimedean.RealStandardEllipticCartan
