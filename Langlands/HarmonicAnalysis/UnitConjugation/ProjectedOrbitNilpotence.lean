import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentApproximation
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitProjection
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-! # Large projected orbit points near the nilpotent cone after rescaling -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set

variable {F R : Type*} [NontriviallyNormedField F] [NormedRing R] [NormedAlgebra F R]
  [IsUltrametricDist R] [completeF : CompleteSpace F] [finiteR : FiniteDimensional F R]
  [properR : ProperSpace R]

/-- A closed annulus in the range of the projection. -/
def projectedAnnulus (p : R →L[F] R) (d : F) : Set R :=
  Metric.closedBall 0 1 ∩
    ((LinearMap.range p.toLinearMap : Set R) ∩ {x | 1 / ‖d‖ ≤ ‖x‖})

/-- Large projected points of an almost fixed orbit that meets a compact conjugacy
saturation have a nonzero rescaling in every open neighborhood of the nilpotent points
of the annulus. The lower bound on size is relative to the lattice bound. -/
def ProjectedOrbitNearNilpotentsStatement [IsUltrametricDist R] [CompleteSpace F]
    [FiniteDimensional F R] [ProperSpace R] (p : R →L[F] R) (d : F)
    (ω V : Set R) (C : ℝ) : Prop :=
  1 < ‖d‖ → IsCompact ω → IsOpen V → 0 ≤ C →
  (∀ x ∈ projectedAnnulus p d, IsNilpotent x → x ∈ V) →
  ∃ t > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ (K : Subgroup Rˣ) (L : AddSubgroup R) (X : R) (β : R → R) (a δ : ℝ),
    (∀ k ∈ K, ∀ l ∈ L, conjugationHomeomorph k l ∈ L) →
    (∀ l ∈ L, ‖l‖ ≤ a) →
    (∀ k ∈ K, ∀ x : R, ‖conjugationHomeomorph k x - x‖ ≤ δ * ‖x‖) →
    (∀ x : R, ‖x - p x‖ ≤ C * ‖β x - x‖) → δ < η →
    (∃ X₀ ∈ conjugationCosetOrbit K L X, β X₀ ∈ conjugationCosetOrbit K L X) →
    (∃ Z ∈ conjugationCosetOrbit K L X, Z ∈ conjugationSaturation ω) →
    ∀ Y ∈ conjugationCosetOrbit K L X, t * max 1 a < ‖p Y‖ →
      ∃ c : F, c ≠ 0 ∧ c • p Y ∈ projectedAnnulus p d ∩ V

omit properR in
private theorem norm_eq_of_orbit_projection_bound (y x : R)
    (A b : ℝ) (hA : 0 ≤ A) (hb : b < 1) (hy : A < ‖y‖)
    (h : ‖y - x‖ ≤ max A (b * ‖x‖)) : ‖y‖ = ‖x‖ := by
  have hxy : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa only [sub_add_cancel] using IsUltrametricDist.norm_add_le_max (y - x) x
  have hx : A < ‖x‖ := by
    by_contra! hxa
    have hb' : b * ‖x‖ ≤ ‖x‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb.le (norm_nonneg x)
    exact hy.not_ge (hxy.trans (max_le (h.trans (max_le le_rfl (hb'.trans hxa))) hxa))
  have hxpos : 0 < ‖x‖ := hA.trans_lt hx
  have hd : ‖y - x‖ < ‖x‖ := h.trans_lt <| max_lt hx (by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hb hxpos)
  have hne : ‖y - x‖ ≠ ‖x‖ := hd.ne
  simpa only [sub_add_cancel, max_eq_right hd.le] using
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne

theorem projectedOrbitNearNilpotents (p : R →L[F] R) (d : F) (ω V : Set R) (C : ℝ) :
    ProjectedOrbitNearNilpotentsStatement p d ω V C := by
  intro hd hω hV hC hnil
  have hK : IsCompact (projectedAnnulus p d) :=
    (isCompact_closedBall _ _).inter_right
      ((LinearMap.range p.toLinearMap).closed_of_finiteDimensional.inter
        (isClosed_le continuous_const continuous_norm))
  obtain ⟨ε, hε, hApprox⟩ := nilpotentApproximation (F := F) (id : R → R)
    (projectedAnnulus p d) V ω continuous_id hK hV hω hnil
  let D := max 1 (max ‖p‖ C)
  have hD : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  let t := D + D / ε
  have hDt : D < t := lt_add_of_pos_right _ (div_pos hDpos hε)
  have hεt : D < ε * t := by
    have hcalc : ε * t = ε * D + D := by
      dsimp only [t]
      rw [mul_add, mul_div_cancel₀ _ hε.ne']
    rw [hcalc]
    exact lt_add_of_pos_left _ (mul_pos hε hDpos)
  refine ⟨t, hDpos.trans hDt, min 1 ε / D, div_pos (lt_min zero_lt_one hε) hDpos, ?_⟩
  intro K L X β a δ hKL hL hconj hβ hδ hAlmost hSaturation Y hY hYlarge
  obtain ⟨X₀, hX₀, _, _, hProj⟩ := almostFixedOrbitProjection K L X p β a δ C hKL hL hconj hC hβ hAlmost
  obtain ⟨Z, hZ, hZω⟩ := hSaturation
  obtain ⟨g, W, hW, hz⟩ := mem_conjugationSaturation_iff.mp hZω
  change conjugationHomeomorph g W = Z at hz
  have hb : D * δ < min 1 ε := by
    calc
      D * δ < D * (min 1 ε / D) := mul_lt_mul_of_pos_left hδ hDpos
      _ = _ := mul_div_cancel₀ _ hDpos.ne'
  have hB (U : R) (hU : U ∈ conjugationCosetOrbit K L X) :
      ‖p Y - U‖ ≤ max (D * a) ((D * δ) * ‖X₀‖) := by
    have h := hProj Y hY U hU
    change ‖p Y - U‖ ≤ D * max a (δ * ‖X₀‖) at h
    rwa [mul_max_of_nonneg _ _ hDpos.le, ← mul_assoc] at h
  have hDa : D * a < ‖p Y‖ := calc
    _ ≤ D * max 1 a := mul_le_mul_of_nonneg_left (le_max_right _ _) hDpos.le
    _ < t * max 1 a := mul_lt_mul_of_pos_right hDt (zero_lt_one.trans_le (le_max_left _ _))
    _ < _ := hYlarge
  have hnorm : ‖p Y‖ = ‖X₀‖ := by
    have ha : 0 ≤ a := (norm_nonneg _).trans (hL 0 L.zero_mem)
    exact norm_eq_of_orbit_projection_bound (p Y) X₀ (D * a) (D * δ)
      (mul_nonneg hDpos.le ha) (hb.trans_le (min_le_left _ _)) hDa (hB X₀ hX₀)
  have hYne : p Y ≠ 0 := by
    have hpos := (mul_pos (hDpos.trans hDt) (zero_lt_one.trans_le (le_max_left 1 a))).trans hYlarge
    exact norm_pos_iff.mp hpos
  obtain ⟨c, hc, hcUpper, hcLower, _⟩ := rescale_to_shell hd zero_lt_one hYne
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcY : ‖c‖ * ‖p Y‖ ≤ 1 := by simpa only [← norm_smul] using hcUpper.le
  have hKc : c • p Y ∈ projectedAnnulus p d := by
    refine ⟨?_, Submodule.smul_mem _ _ ⟨Y, rfl⟩, hcLower⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hcUpper.le
  have hscale : ‖c‖ * (D * max 1 a) < ε := calc
    _ < ‖c‖ * ((ε * t) * max 1 a) := mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_right hεt (zero_lt_one.trans_le (le_max_left _ _))) hc0
    _ = ε * (‖c‖ * (t * max 1 a)) := by ring
    _ < ε * (‖c‖ * ‖p Y‖) := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hYlarge hc0) hε
    _ ≤ ε := by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hcY hε.le)
  have hcε : ‖c‖ < ε := by
    apply lt_of_le_of_lt _ hscale
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_mul_of_one_le_of_one_le hD (le_max_left 1 a)) hc0.le
  have hcl : ‖c‖ * (D * a) < ε :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right 1 a) hDpos.le)
      hc0.le).trans_lt hscale
  have hcd : ‖c‖ * ((D * δ) * ‖X₀‖) < ε := calc
    _ = (D * δ) * (‖c‖ * ‖p Y‖) := by rw [← hnorm]; ring
    _ < ε * (‖c‖ * ‖p Y‖) := mul_lt_mul_of_pos_right (hb.trans_le (min_le_right _ _))
      (mul_pos hc0 (norm_pos_iff.mpr hYne))
    _ ≤ ε := by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hcY hε.le)
  have herr : ‖c • conjugationHomeomorph g W - c • p Y‖ < ε := by
    rw [hz, ← smul_sub, norm_smul, norm_sub_rev]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hB Z hZ) hc0.le)
    rw [mul_max_of_nonneg _ _ hc0.le]
    exact max_lt hcl hcd
  exact ⟨c, hc, hKc, hApprox c (c • p Y) hKc g W hW hcε herr⟩

end Langlands.HarmonicAnalysis.UnitConjugation
