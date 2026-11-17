import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzCompactLifting
import Langlands.Representation.Whittaker.Algebraic
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! # Right translations on the projected left-invariant Schwartz space -/

noncomputable section

universe uG

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Nonempty (CompactOpenSubgroup Γ)]
  {Ξ σ : Γ → ℝ} {A : Subgroup Γ} [MeasurableSpace A]

/-- The prescribed left-invariant part of a Schwartz subspace. -/
def schwartzLeftLevel (E : Submodule ℂ (Space Ξ σ)) (H : Subgroup Γ) :
    Submodule ℂ (Space Ξ σ) :=
  E ⊓ (leftInvariantFunctionSubmodule H).comap Space.toFunLinear

/-- The prescribed bi-invariant part of a Schwartz subspace. -/
def schwartzBiLevel (E : Submodule ℂ (Space Ξ σ)) (H : Subgroup Γ) :
    Submodule ℂ (Space Ξ σ) :=
  E ⊓ (biInvariantFunctionSubmodule H).comap Space.toFunLinear

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Nonempty (CompactOpenSubgroup Γ)] in
/-- Central projection preserves left invariance. -/
theorem IsLeftInvariant.centralProjection (hA : A ≤ Subgroup.center Γ)
    (muA : Measure A) (χ : A →* ℂˣ) {H : Subgroup Γ} {f : Γ → ℂ}
    (hf : IsLeftInvariant H f) : IsLeftInvariant H (centralProjection muA χ f) := by
  intro h hh x
  apply integral_congr_ae
  filter_upwards [] with a
  have he : (a : Γ) * (h * x) = h * ((a : Γ) * x) := by
    rw [← mul_assoc, ← Subgroup.mem_center_iff.mp (hA a.property) h, mul_assoc]
  simp only [he, hf h hh]

omit [Nonempty (CompactOpenSubgroup Γ)] in
/-- Right translations preserve the prescribed left-invariant part. -/
theorem schwartzLeftLevel_translate_right (ht : TranslationWeights Ξ σ)
    (E : Submodule ℂ (Space Ξ σ)) (hE : IsTranslationStable ht E)
    (H : Subgroup Γ) (g : Γ) {φ : Space Ξ σ} (hφ : φ ∈ schwartzLeftLevel E H) :
    Space.translate ht g 1 φ ∈ schwartzLeftLevel E H := by
  refine ⟨hE g 1 φ hφ.1, ?_⟩
  intro h hh x
  change φ (1⁻¹ * (h * x) * g) = φ (1⁻¹ * x * g)
  have he := hφ.2 h hh (x * g)
  change φ (h * (x * g)) = φ (x * g) at he
  simpa only [inv_one, one_mul, mul_assoc]
    using he

/-- The actual right action on the span of the raw central image of a left level. -/
def projectedLeftSubrepresentation (ht : TranslationWeights Ξ σ)
    (E : Submodule ℂ (Space Ξ σ)) (hE : IsTranslationStable ht E)
    (hA : A ≤ Subgroup.center Γ) (muA : Measure A) (χ : A →* ℂˣ)
    (H : Subgroup Γ) : Subrepresentation (Whittaker.rightTranslation ℂ Γ) where
  toSubmodule := schwartzCentralIntegralSpan (schwartzLeftLevel E H) muA χ
  apply_mem_toSubmodule g := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφ, rfl⟩ := hf
      apply Submodule.subset_span
      refine ⟨Space.translate ht g 1 φ,
        schwartzLeftLevel_translate_right ht E hE H g hφ, ?_⟩
      rw [Space.coe_translate, centralProjection_translate hA]
      funext x
      simp only [translate_apply, inv_one, one_mul]
      rfl
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add f f' _ _ hf hf' => rw [map_add]; exact Submodule.add_mem _ hf hf'
    | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

variable (ht : TranslationWeights Ξ σ) (E : Submodule ℂ (Space Ξ σ))
  (hE : IsTranslationStable ht E) (hA : A ≤ Subgroup.center Γ)
  (muA : Measure A) (χ : A →* ℂˣ)
  (hc : CentralIntegralConvergesOn E muA χ) (H : Subgroup Γ)

include hc

/-- Convergence identifies this representation's vectors with actual raw images. -/
theorem projectedLeftSubrepresentation_mem_image
    (f : (projectedLeftSubrepresentation ht E hE hA muA χ H).toSubmodule) :
    (f : Γ → ℂ) ∈ schwartzCentralIntegralImage (schwartzLeftLevel E H) muA χ := by
  have hcH : CentralIntegralConvergesOn (schwartzLeftLevel E H) muA χ :=
    fun φ hφ x => hc φ hφ.1 x
  exact (coe_schwartzCentralIntegralSpan_eq_image
    (schwartzLeftLevel E H) muA χ hcH) ▸ f.property

/-- Every vector of the actual projected representation has an open stabilizer. -/
theorem isSmooth_projectedLeftSubrepresentation :
    IsSmooth (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation := by
  intro f
  obtain ⟨φ, _, hφ⟩ := projectedLeftSubrepresentation_mem_image ht E hE hA muA χ hc H f
  obtain ⟨J, hJ⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem φ)
  have hJf : IsBiInvariant J.toSubgroup (f : Γ → ℂ) :=
    hφ ▸ hJ.1.centralProjection hA χ
  refine ⟨J.1, ?_⟩
  intro j
  apply Subtype.ext
  funext x
  change (f : Γ → ℂ) (x * (j : Γ)) = (f : Γ → ℂ) x
  simpa only [one_mul] using hJf 1 J.toSubgroup.one_mem j j.property x

/-- Left invariance survives projection for every vector of the representation. -/
theorem isLeftInvariant_projectedLeftSubrepresentation
    (f : (projectedLeftSubrepresentation ht E hE hA muA χ H).toSubmodule) :
    IsLeftInvariant H (f : Γ → ℂ) := by
  obtain ⟨φ, hφ, hφf⟩ :=
    projectedLeftSubrepresentation_mem_image ht E hE hA muA χ hc H f
  rw [← hφf]
  exact hφ.2.centralProjection hA muA χ

/-- The center acts on this actual function representation by the specified character. -/
theorem projectedLeftSubrepresentation_central [MeasurableMul A] [muA.IsMulRightInvariant]
    (a : A) (f : (projectedLeftSubrepresentation ht E hE hA muA χ H).toSubmodule) :
    (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation a f =
      (χ a : ℂ) • f := by
  obtain ⟨φ, _, hφ⟩ := projectedLeftSubrepresentation_mem_image ht E hE hA muA χ hc H f
  apply Subtype.ext
  funext x
  change (f : Γ → ℂ) (x * (a : Γ)) = (χ a : ℂ) * (f : Γ → ℂ) x
  rw [← hφ, Subgroup.mem_center_iff.mp (hA a.property) x, centralProjection_mul_left]

/-- Compact averaging places a fixed vector in a compact intersection level span. -/
theorem projectedLeftSubrepresentation_fixed_mem_level
    (H₀ J : OpenSubgroup Γ) (hH₀ : IsCompact (H₀ : Set Γ))
    (f : fixedVectors
      (projectedLeftSubrepresentation ht E hE hA muA χ H₀.toSubgroup).toRepresentation
      J.toSubgroup) :
    (f.val.val : Γ → ℂ) ∈
      schwartzCentralIntegralSpan (schwartzBiLevel E (H₀ ⊓ J).toSubgroup) muA χ := by
  obtain ⟨φ, hφ, hφf⟩ :=
    projectedLeftSubrepresentation_mem_image ht E hE hA muA χ hc H₀.toSubgroup f.val
  have hf : (f.val.val : Γ → ℂ) ∈ schwartzCentralIntegralImage E muA χ :=
    ⟨φ, hφ.1, hφf⟩
  have hleft := isLeftInvariant_projectedLeftSubrepresentation
    ht E hE hA muA χ hc H₀.toSubgroup f.val
  have hbi : IsBiInvariant (H₀ ⊓ J).toSubgroup (f.val.val : Γ → ℂ) := by
    intro h₁ hh₁ h₂ hh₂ x
    have hright := congrArg (fun z => (z.val : Γ → ℂ) x)
      (f.property ⟨h₂, hh₂.2⟩)
    change (f.val.val : Γ → ℂ) (x * h₂) = (f.val.val : Γ → ℂ) x at hright
    rw [mul_assoc, hleft h₁ hh₁.1, hright]
  obtain ⟨ψ, hψ, hψbi, hψf⟩ := exists_biInvariant_central_preimage
    ht E hE hA muA χ hc (H₀ ⊓ J) (hH₀.inter_right J.isClosed) hf hbi
  exact Submodule.subset_span ⟨ψ, ⟨hψ, hψbi⟩, hψf⟩

set_option maxHeartbeats 800000 in
/-- VIII.4.1's finite compact level spans imply admissibility of this actual
right-translation representation. No finite spectral support is assumed. -/
theorem isAdmissible_projectedLeftSubrepresentation
    (H₀ : OpenSubgroup Γ) (hH₀ : IsCompact (H₀ : Set Γ))
    (hfinite : ∀ J : OpenSubgroup Γ, IsCompact (J : Set Γ) →
      FiniteDimensional ℂ
        (schwartzCentralIntegralSpan (schwartzBiLevel E J.toSubgroup) muA χ)) :
    IsAdmissible
      (projectedLeftSubrepresentation ht E hE hA muA χ H₀.toSubgroup).toRepresentation := by
  refine ⟨isSmooth_projectedLeftSubrepresentation ht E hE hA muA χ hc H₀.toSubgroup, ?_⟩
  intro J
  let V := (projectedLeftSubrepresentation ht E hE hA muA χ H₀.toSubgroup).toSubmodule
  let W := schwartzCentralIntegralSpan (schwartzBiLevel E (H₀ ⊓ J).toSubgroup) muA χ
  let : FiniteDimensional ℂ W := hfinite (H₀ ⊓ J) (hH₀.inter_right J.isClosed)
  let ι : fixedVectors
      (projectedLeftSubrepresentation ht E hE hA muA χ H₀.toSubgroup).toRepresentation
      J.toSubgroup →ₗ[ℂ] (Γ → ℂ) :=
    V.subtype.comp (fixedVectors _ J.toSubgroup).subtype
  let ιW := ι.codRestrict W
    (projectedLeftSubrepresentation_fixed_mem_level ht E hE hA muA χ hc H₀ J hH₀)
  apply Module.Finite.of_injective ιW
  intro f g hfg
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : W => (z : Γ → ℂ)) hfg

end Langlands.HarishChandraSchwartz
