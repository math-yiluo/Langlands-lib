import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

noncomputable section

open scoped InnerProductSpace

namespace Langlands.Archimedean

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private theorem selfAdjoint_scalar (ρ : G →* (E →L[ℂ] E))
    (hirr : IsTopologicallyIrreducible ρ) {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (hcomm : ∀ g, Commute A (ρ g)) :
    ∃ r : ℝ, A = (r : ℂ) • ContinuousLinearMap.id ℂ E := by
  let : Nontrivial E := hirr.1
  have hordered (x y : ℝ) (hx : x ∈ spectrum ℝ A) (hy : y ∈ spectrum ℝ A)
      (hxy : x < y) : False := by
    let t := (x + y) / 2
    have hxt : x < t := by dsimp [t]; linarith
    have hty : t < y := by dsimp [t]; linarith
    let f : ℝ → ℝ := fun s => max (t - s) 0
    let g : ℝ → ℝ := fun s => max (s - t) 0
    have hf : Continuous f := (continuous_const.sub continuous_id).max continuous_const
    have hg : Continuous g := (continuous_id.sub continuous_const).max continuous_const
    have hfA : cfc f A ≠ 0 := by
      intro hz
      rw [← cfc_zero ℝ A] at hz
      have h := eqOn_of_cfc_eq_cfc hz hf.continuousOn continuousOn_const hA hx
      dsimp [f] at h
      rw [max_eq_left (sub_nonneg.mpr hxt.le)] at h
      exact (sub_ne_zero.mpr hxt.ne') h
    have hgA : cfc g A ≠ 0 := by
      intro hz
      rw [← cfc_zero ℝ A] at hz
      have h := eqOn_of_cfc_eq_cfc hz hg.continuousOn continuousOn_const hA hy
      dsimp [g] at h
      rw [max_eq_left (sub_nonneg.mpr hty.le)] at h
      exact (sub_ne_zero.mpr hty.ne') h
    have hfg : cfc f A * cfc g A = 0 := by
      rw [← cfc_mul f g A hf.continuousOn hg.continuousOn, ← cfc_zero ℝ A]
      apply cfc_congr
      intro s _
      rcases le_total s t with hst | hts
      · simp [g, max_eq_right (sub_nonpos.mpr hst)]
      · simp [f, max_eq_right (sub_nonpos.mpr hts)]
    have hinv : ∀ a, ∀ v ∈ (cfc f A).ker, ρ a v ∈ (cfc f A).ker := by
      intro a v hv
      change cfc f A v = 0 at hv
      change cfc f A (ρ a v) = 0
      have h := (hA.commute_cfc (hcomm a) f).eq
      change (cfc f A * ρ a) v = 0
      rw [h]
      change ρ a (cfc f A v) = 0
      rw [hv, map_zero]
    rcases hirr.2 _ (cfc f A).isClosed_ker hinv with hb | ht
    · apply hgA
      ext v
      have hv : cfc g A v ∈ (cfc f A).ker := by
        change (cfc f A * cfc g A) v = 0
        rw [hfg]
        rfl
      simpa [hb] using hv
    · exact hfA (ContinuousLinearMap.ext fun v =>
        LinearMap.congr_fun (LinearMap.ker_eq_top.mp ht) v)
  obtain ⟨x, hx⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hs : spectrum ℝ A ⊆ {x} := by
    intro y hy
    exact le_antisymm (le_of_not_gt (hordered x y hx hy))
      (le_of_not_gt (hordered y x hy hx))
  refine ⟨x, ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, Complex.coe_smul, ContinuousLinearMap.one_def] using
    CFC.eq_algebraMap_of_spectrum_subset_singleton A x hs hA

/-- A bounded operator commuting with a topologically irreducible unitary representation is
scalar. The action need not be continuous for this conclusion. -/
theorem exists_eq_scalar_of_unitary_commute (ρ : G →* (E →L[ℂ] E))
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    (hirr : IsTopologicallyIrreducible ρ) (B : E →L[ℂ] E)
    (hB : ∀ g, Commute B (ρ g)) :
    ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ E := by
  have hinv (g : G) : star (ρ g) = ρ g⁻¹ := by
    have h : star (ρ g) * ρ g = 1 :=
      (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp (hunit g)
    calc
      star (ρ g) = (star (ρ g) * ρ g) * ρ g⁻¹ := by
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = ρ g⁻¹ := by rw [h, one_mul]
  have hstar (g : G) : Commute (star B) (ρ g) := by
    simpa only [hinv, inv_inv] using commute_star_star.mpr (hB g⁻¹)
  obtain ⟨r, hr⟩ := selfAdjoint_scalar ρ hirr (realPart B).2 fun g => by
    rw [realPart_apply_coe]
    exact ((hB g).add_left (hstar g)).smul_left _
  obtain ⟨s, hs⟩ := selfAdjoint_scalar ρ hirr (imaginaryPart B).2 fun g => by
    rw [imaginaryPart_apply_coe]
    exact (((hB g).sub_left (hstar g)).smul_left (2 : ℝ)⁻¹).smul_left _
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart B, hr, hs, smul_smul, add_smul]


end Langlands.Archimedean
