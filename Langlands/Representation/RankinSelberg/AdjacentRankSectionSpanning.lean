import Langlands.Representation.RankinSelberg.AdjacentRankFrameOrbit
import Langlands.Representation.RankinSelberg.AdjacentRankCompactSection
import Langlands.Representation.Induction.CompactLocalSectionSpanningProof

/-! Spanning by compact rectangular averages for the actual adjacent-rank lower parabolic. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix Induction

universe uF uV

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The trivial outer smooth character, used before twisting the sections. -/
def adjacentRankUnitCharacter : SmoothCharacter ℂ (GeneralLinear (r + 2) K) :=
  ⟨1, by simp⟩

private abbrev P := (adjacentRankLowerShape r).oppositeParabolic K
private abbrev a : P (K := K) (r := r) →* GeneralLinear (r + 1) K :=
  adjacentRankLowerLargeProjection

variable [MeasurableSpace (GeneralLinear (r + 1) K)]
  [OpensMeasurableSpace (GeneralLinear (r + 1) K)]
  (μ : Measure (GeneralLinear (r + 1) K)) [IsFiniteMeasureOnCompacts μ]
  (ρ : Representation ℂ (GeneralLinear (r + 1) K) V) (hρ : IsSmooth ρ)
  (ξ : GeneralLinear (r + 1) K →* ℂˣ)
  (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))

private abbrev τ :=
  adjacentRankCompactSectionRepresentation (P (K := K) (r := r)) a ρ ξ
    adjacentRankUnitCharacter

/-- A fixed vector makes the entire inner orbit integrand constant on the slice. -/
theorem adjacentRankFrameSlice_integrand
    (J : OpenSubgroup (GeneralLinear (r + 2) K))
    (hJ : IsCompact (J : Set (GeneralLinear (r + 2) K))) (v : V)
    (hv : v ∈ fixedVectors (τ ρ ξ) (conjOpenSubgroup P J 1).toSubgroup)
    (h : GeneralLinear (r + 1) K) :
    adjacentRankCompactIntegrand ρ hρ ξ hξ (adjacentRankFrameOrbitTest J hJ) v 1 h =
      (adjacentRankFrameSlice J.toSubgroup : Set (GeneralLinear (r + 1) K)).indicator
        (fun _ => v) h := by
  classical
  rw [adjacentRankCompactIntegrand_apply, Units.val_one, Matrix.mul_one,
    adjacentRankFrameOrbitTest_apply]
  change ((adjacentRankFrame '' (J.toSubgroup : Set _)).indicator
      (fun _ => (1 : ℂ)) (rectangularJoin h.val 0) * (ξ h : ℂ)) • ρ h⁻¹ v = _
  by_cases hh : h ∈ adjacentRankFrameSlice J.toSubgroup
  · have hm := (mem_adjacentRankFrameSlice_iff J.toSubgroup h).mp hh
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hh, one_mul]
    obtain ⟨q, hq, hqa⟩ := hh
    have hqi : q⁻¹ ∈ conjOpenSubgroup P J 1 := by
      apply mem_conjOpenSubgroup.mpr
      simpa using J.inv_mem hq
    have he := hv ⟨q⁻¹, hqi⟩
    change (((1 : GeneralLinear (r + 2) K →* ℂˣ) q⁻¹.val *
      (ξ (a q⁻¹))⁻¹ : ℂˣ) : ℂ) • ρ (a q⁻¹) v = v at he
    simpa only [MonoidHom.one_apply, one_mul, map_inv, hqa, inv_inv] using he
  · have hm := fun hm => hh ((mem_adjacentRankFrameSlice_iff J.toSubgroup h).mpr hm)
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hh, zero_mul, zero_smul]

/-- At the identity the orbit average is the finite Haar mass of the slice times the vector. -/
theorem adjacentRankFrameSlice_average
    (J : OpenSubgroup (GeneralLinear (r + 2) K))
    (hJ : IsCompact (J : Set (GeneralLinear (r + 2) K))) (v : V)
    (hv : v ∈ fixedVectors (τ ρ ξ) (conjOpenSubgroup P J 1).toSubgroup) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ (adjacentRankFrameOrbitTest J hJ) v 1 =
      ((μ (adjacentRankFrameSlice J.toSubgroup : Set _)).toReal : ℂ) • v := by
  have hs := (isOpen_adjacentRankFrameSlice J).measurableSet
  have he : adjacentRankCompactIntegrand ρ hρ ξ hξ (adjacentRankFrameOrbitTest J hJ) v 1 =
      (SimpleFunc.const (GeneralLinear (r + 1) K) v).restrict
        (adjacentRankFrameSlice J.toSubgroup : Set _) := by
    ext h
    rw [adjacentRankFrameSlice_integrand ρ hρ ξ hξ J hJ v hv,
      SimpleFunc.restrict_apply _ hs]
    rfl
  unfold adjacentRankCompactAverage
  rw [he, AlgebraicIntegral.integral_indicator_const _ hs]

omit [OpensMeasurableSpace (GeneralLinear (r + 1) K)] in
/-- The compact open inner slice has nonzero finite positive mass for a positive measure. -/
theorem adjacentRankFrameSlice_mass_ne_zero [μ.IsOpenPosMeasure]
    (J : OpenSubgroup (GeneralLinear (r + 2) K))
    (hJ : IsCompact (J : Set (GeneralLinear (r + 2) K))) :
    ((μ (adjacentRankFrameSlice J.toSubgroup : Set _)).toReal : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos
    ((isOpen_adjacentRankFrameSlice J).measure_pos μ
      ⟨1, (adjacentRankFrameSlice J.toSubgroup).one_mem⟩).ne'
        (isCompact_adjacentRankFrameSlice J hJ).measure_ne_top).ne'

variable (hμ : ∀ q : P (K := K) (r := r),
  MeasurePreserving (fun h : GeneralLinear (r + 1) K => h * a q) μ μ)

/-- The rectangular tensor-section map for the actual ordered lower parabolic. -/
def adjacentRankLowerSectionTensor
    (θ : SmoothCharacter ℂ (GeneralLinear (r + 2) K)) :
    TensorProduct ℂ (adjacentRankCompactTests (r + 1) K) V →ₗ[ℂ]
      SmoothFunctions P (adjacentRankCompactSectionRepresentation P a ρ ξ θ) :=
  adjacentRankCompactSectionTensor μ ρ hρ ξ hξ θ P a
    adjacentRankLower_rectangular_mul hμ

/-- The orbit average is the standard identity-centered local section, scaled by
the finite mass of its inner slice. -/
theorem adjacentRankFrameOrbit_section
    (J : OpenSubgroup (GeneralLinear (r + 2) K))
    (hJ : IsCompact (J : Set (GeneralLinear (r + 2) K))) (v : V)
    (hv : v ∈ fixedVectors (τ ρ ξ) (conjOpenSubgroup P J 1).toSubgroup) :
    adjacentRankCompactSection μ ρ hρ ξ hξ adjacentRankUnitCharacter P a
        adjacentRankLower_rectangular_mul hμ (adjacentRankFrameOrbitTest J hJ) v =
      ((μ (adjacentRankFrameSlice J.toSubgroup : Set _)).toReal : ℂ) •
        (compactDoubleCosetSection P (τ ρ ξ) J hJ 1 v hv).val := by
  classical
  let c : ℂ := (μ (adjacentRankFrameSlice J.toSubgroup : Set _)).toReal
  let Φ := adjacentRankFrameOrbitTest J hJ
  have hright (j : J) : adjacentRankCompactTestTranslate j.val Φ = Φ := by
    apply Subtype.ext
    ext M
    exact adjacentRankFrameOrbitTest_right J hJ j M
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change adjacentRankCompactSectionValue μ ρ hρ ξ hξ adjacentRankUnitCharacter Φ v g =
    c • eval P (τ ρ ξ) (compactDoubleCosetSection P (τ ρ ξ) J hJ 1 v hv).val g
  have he (x : GeneralLinear (r + 2) K) :
      adjacentRankCompactSectionValue μ ρ hρ ξ hξ adjacentRankUnitCharacter Φ v x =
        adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v x := by
    simp [adjacentRankCompactSectionValue, adjacentRankUnitCharacter]
  rw [he]
  by_cases hg : ∃ (q : P (K := K) (r := r)) (j : J), g = q.val * j.val
  · obtain ⟨q, j, rfl⟩ := hg
    rw [adjacentRankCompactAverage_right, hright j]
    have hleft := eval_covariant P (τ ρ ξ)
      (adjacentRankCompactSection μ ρ hρ ξ hξ adjacentRankUnitCharacter P a
        adjacentRankLower_rectangular_mul hμ Φ v) q 1
    change adjacentRankCompactSectionValue μ ρ hρ ξ hξ adjacentRankUnitCharacter Φ v
        (q.val * 1) =
      (τ ρ ξ) q
        (adjacentRankCompactSectionValue μ ρ hρ ξ hξ adjacentRankUnitCharacter Φ v 1)
      at hleft
    simp only [mul_one, he] at hleft
    rw [hleft, adjacentRankFrameSlice_average μ ρ hρ ξ hξ J hJ v hv, map_smul]
    congr 1
    simpa only [mul_one] using
      (compactDoubleCosetSection_apply P (τ ρ ξ) J hJ 1 v hv q j).symm
  · have hzero : adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g = 0 := by
      ext h
      have hm : rectangularJoin h.val 0 * g.val ∉
          adjacentRankFrame '' (J.toSubgroup : Set _) := by
        intro hm
        obtain ⟨q, j, heq, -⟩ :=
          (adjacentRankFrame_orbit_iff J.toSubgroup h g).mp hm
        exact hg ⟨q, j, heq⟩
      simp only [adjacentRankCompactIntegrand_apply, Φ, adjacentRankFrameOrbitTest_apply]
      change ((adjacentRankFrame '' (J.toSubgroup : Set _)).indicator
        (fun _ => (1 : ℂ)) (rectangularJoin h.val 0 * g.val) * (ξ h : ℂ)) •
          ρ h⁻¹ v = 0
      rw [Set.indicator_of_notMem hm, zero_mul, zero_smul]
    have hlocal : eval P (τ ρ ξ)
        (compactDoubleCosetSection P (τ ρ ξ) J hJ 1 v hv).val g = 0 := by
      by_contra hn
      obtain ⟨j, hj, hjg⟩ := compactDoubleCosetSection_support_subset P (τ ρ ξ)
        J hJ 1 v hv ⟨g, hn, rfl⟩
      have hq : g * (1 * j)⁻¹ ∈ P :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact hjg)
      exact hg ⟨⟨_, hq⟩, ⟨j, hj⟩, by simp⟩
    simp [adjacentRankCompactAverage, hzero, hlocal]

/-- Every right translate of a standard compact local section lies in the
image of the rectangular-test tensor map, with trivial outer character. -/
theorem adjacentRankFrameOrbit_translate_mem_range [μ.IsOpenPosMeasure]
    (J : OpenSubgroup (GeneralLinear (r + 2) K))
    (hJ : IsCompact (J : Set (GeneralLinear (r + 2) K))) (v : V)
    (hv : v ∈ fixedVectors (τ ρ ξ) (conjOpenSubgroup P J 1).toSubgroup)
    (g : GeneralLinear (r + 2) K) :
    (compactInduced P (τ ρ ξ) g
      (compactDoubleCosetSection P (τ ρ ξ) J hJ 1 v hv)).val ∈
      LinearMap.range (adjacentRankCompactSectionTensor μ ρ hρ ξ hξ
        adjacentRankUnitCharacter P a adjacentRankLower_rectangular_mul hμ) := by
  let c : ℂ := (μ (adjacentRankFrameSlice J.toSubgroup : Set _)).toReal
  have hc : c ≠ 0 := adjacentRankFrameSlice_mass_ne_zero μ J hJ
  refine ⟨c⁻¹ • TensorProduct.tmul ℂ
    (adjacentRankCompactTestTranslate g (adjacentRankFrameOrbitTest J hJ)) v, ?_⟩
  rw [map_smul, adjacentRankCompactSectionTensor_tmul]
  have ht := adjacentRankCompactSection_right μ ρ hρ ξ hξ adjacentRankUnitCharacter
    P a adjacentRankLower_rectangular_mul hμ (adjacentRankFrameOrbitTest J hJ) v g
  change _ = (1 : ℂ) • _ at ht
  rw [one_smul] at ht
  rw [← ht, adjacentRankFrameOrbit_section μ ρ hρ ξ hξ hμ J hJ v hv,
    map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rfl

/-- All compactly induced vectors are rectangular tensor averages. This uses
the existing local-section spanning theorem and a compact open subgroup basis. -/
theorem adjacentRankCompactSectionTensor_covers_compact [μ.IsOpenPosMeasure]
    (hbasis : ∀ O : Set (GeneralLinear (r + 2) K), IsOpen O → 1 ∈ O →
      ∃ J : OpenSubgroup (GeneralLinear (r + 2) K),
        IsCompact (J : Set (GeneralLinear (r + 2) K)) ∧
        (J : Set (GeneralLinear (r + 2) K)) ⊆ O)
    (f : CompactFunctions P (τ ρ ξ)) :
    f.val ∈ LinearMap.range (adjacentRankCompactSectionTensor μ ρ hρ ξ hξ
      adjacentRankUnitCharacter P a adjacentRankLower_rectangular_mul hμ) := by
  let N : Submodule ℂ (CompactFunctions P (τ ρ ξ)) :=
    (LinearMap.range (adjacentRankCompactSectionTensor μ ρ hρ ξ hξ
      adjacentRankUnitCharacter P a adjacentRankLower_rectangular_mul hμ)).comap
        (compactInclusion P (τ ρ ξ)).toLinearMap
  have hs := compactLocalSectionSpanning (GeneralLinear (r + 2) K) hbasis P
    ((adjacentRankLowerShape r).isClosed_oppositeParabolic K) V (τ ρ ξ)
  have hle : ⊤ ≤ N := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, J, hJ, v, hv, rfl⟩
    exact adjacentRankFrameOrbit_translate_mem_range μ ρ hρ ξ hξ hμ J hJ v hv g
  exact hle (Submodule.mem_top)

end Langlands.RankinSelberg
