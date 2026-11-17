import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzProjectedRepresentation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleCoefficientSpace
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! # Coefficients of the projected right-translation representation

For an admissible projected right-translation representation on the span of the raw
central image of a left level, every matrix coefficient is a raw central integral of the
ambient translation-stable Schwartz subspace. The proof uses Waldspurger's Lemma I.6.1
(`twoSidedTranslateSpan_eq_coefficientFunctionSpace`) and the equivariance of the central
integral. It uses no convolution identity.
-/

noncomputable section

universe uG

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {Ξ σ : Γ → ℝ} {A : Subgroup Γ} [MeasurableSpace A]

section Translates

/-- Two-sided translates of a raw central integral of a translation-stable subspace are
raw central integrals of the same subspace. -/
theorem translate_mem_schwartzCentralIntegralImage (ht : TranslationWeights Ξ σ)
    {E : Submodule ℂ (Space Ξ σ)} (hE : IsTranslationStable ht E)
    (hA : A ≤ Subgroup.center Γ) (muA : Measure A) (χ : A →* ℂˣ)
    {f : Γ → ℂ} (hf : f ∈ schwartzCentralIntegralImage E muA χ) (g₁ g₂ : Γ) :
    translate g₁ g₂ f ∈ schwartzCentralIntegralImage E muA χ := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  refine ⟨Space.translate ht g₁ g₂ φ, hE g₁ g₂ φ hφ, ?_⟩
  rw [Space.coe_translate, centralProjection_translate hA]

/-- The span `V_{ρ×λ}(f)` of the two-sided translates of such a raw central integral lies
in the span of the raw image. -/
theorem twoSidedTranslateSpan_le_schwartzCentralIntegralSpan (ht : TranslationWeights Ξ σ)
    {E : Submodule ℂ (Space Ξ σ)} (hE : IsTranslationStable ht E)
    (hA : A ≤ Subgroup.center Γ) (muA : Measure A) (χ : A →* ℂˣ)
    {f : Γ → ℂ} (hf : f ∈ schwartzCentralIntegralImage E muA χ) :
    twoSidedTranslateSpan f ≤ schwartzCentralIntegralSpan E muA χ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g₁, g₂⟩, rfl⟩
  exact Submodule.subset_span
    (translate_mem_schwartzCentralIntegralImage ht hE hA muA χ hf g₁ g₂)

end Translates

variable [Nonempty (CompactOpenSubgroup Γ)]
  (ht : TranslationWeights Ξ σ) (E : Submodule ℂ (Space Ξ σ))
  (hE : IsTranslationStable ht E) (hA : A ≤ Subgroup.center Γ)
  (muA : Measure A) (χ : A →* ℂˣ)
  (hc : CentralIntegralConvergesOn E muA χ) (H : Subgroup Γ)

include hc

/-- Under convergence, every vector of the projected representation is a raw central
integral of the ambient subspace `E`. -/
theorem projectedLeftSubrepresentation_mem_ambient_image
    (v : (projectedLeftSubrepresentation ht E hE hA muA χ H).toSubmodule) :
    (v : Γ → ℂ) ∈ schwartzCentralIntegralImage E muA χ :=
  schwartzCentralIntegralImage_mono E muA χ inf_le_left
    (projectedLeftSubrepresentation_mem_image ht E hE hA muA χ hc H v)

/-- If the projected representation is admissible, each of its vectors lies in
Waldspurger's `A_ρ`: it is bi-invariant under a compact open subgroup and right translation
on its right-translate span is admissible. -/
theorem isRightAdmissible_of_mem_projectedLeftSubrepresentation
    (ha : IsAdmissible (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation)
    (v : (projectedLeftSubrepresentation ht E hE hA muA χ H).toSubmodule) :
    IsRightAdmissible (v : Γ → ℂ) := by
  obtain ⟨φ, _, hφv⟩ := projectedLeftSubrepresentation_mem_image ht E hE hA muA χ hc H v
  obtain ⟨J, hJ⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem φ)
  refine ⟨⟨J, hφv ▸ hJ.1.centralProjection hA χ⟩, ?_⟩
  have hle : rightTranslateSpan (v : Γ → ℂ) ≤ projectedLeftSubrepresentation ht E hE hA muA χ H :=
    FiniteVectors.orbitSpan_le _ _ _ v.property
  exact isAdmissible_of_injective (inclusionOfLe hle) (inclusionOfLe_injective hle) ha

/-- **Coefficient closure.** Every matrix coefficient of an admissible projected
right-translation representation lies in the span of the raw central image of the ambient
translation-stable subspace. -/
theorem coefficientFunctionSpace_projectedLeftSubrepresentation_le
    (ha : IsAdmissible (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation) :
    coefficientFunctionSpace
        (SmoothRep.of (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation
          ha.1) ≤
      schwartzCentralIntegralSpan E muA χ := by
  refine iSup_le fun ℓ => ?_
  rintro _ ⟨v, rfl⟩
  have hv := isRightAdmissible_of_mem_projectedLeftSubrepresentation
    ht E hE hA muA χ hc H ha v
  have hle : rightTranslateSpan (v : Γ → ℂ) ≤ projectedLeftSubrepresentation ht E hE hA muA χ H :=
    FiniteVectors.orbitSpan_le _ _ _ v.property
  let ι := inclusionOfLe hle
  let w : (rightTranslateSpan (v : Γ → ℂ)).toSubmodule :=
    ⟨v, mem_rightTranslateSpan_self _⟩
  let ℓ' : SmoothDual (rightTranslateRep hv).representation :=
    ⟨dualIntertwining ι ℓ.val, isSmoothVector_map (dualIntertwining ι) ℓ.property⟩
  have hmem := matrixCoefficient_mem_coefficientFunctionSpace (rightTranslateRep hv) ℓ' w
  rw [← twoSidedTranslateSpan_eq_coefficientFunctionSpace hv] at hmem
  have heq : matrixCoefficient
      (SmoothRep.of (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation
        ha.1).representation ℓ.val v =
      matrixCoefficient (rightTranslateRep hv).representation ℓ'.val w :=
    matrixCoefficient_intertwining ι ℓ.val w
  rw [heq]
  exact twoSidedTranslateSpan_le_schwartzCentralIntegralSpan ht hE hA muA χ
    (projectedLeftSubrepresentation_mem_ambient_image ht E hE hA muA χ hc H v) hmem

/-- Under convergence the span equals the raw image, so every coefficient is a single raw
central integral of the ambient subspace. -/
theorem coefficientFunctionSpace_projectedLeftSubrepresentation_subset_image
    (ha : IsAdmissible (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation) :
    (coefficientFunctionSpace
        (SmoothRep.of (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation
          ha.1) : Set (Γ → ℂ)) ⊆
      schwartzCentralIntegralImage E muA χ := by
  intro f hf
  rw [← coe_schwartzCentralIntegralSpan_eq_image E muA χ hc]
  exact coefficientFunctionSpace_projectedLeftSubrepresentation_le
    ht E hE hA muA χ hc H ha hf

omit hc

/-- The coefficient-closure property recorded as a proposition over all topological groups
with a compact open subgroup: for every translation-stable Schwartz subspace on which the
central integral converges and every subgroup `H` for which the projected right-translation
representation is admissible, its coefficient space lies in the span of the raw central
image of the subspace. It is proved below. -/
def ProjectedCoefficientClosureStatement : Prop :=
  ∀ (Γ : Type uG) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Nonempty (CompactOpenSubgroup Γ)] (Ξ σ : Γ → ℝ) (A : Subgroup Γ) [MeasurableSpace A]
    (ht : TranslationWeights Ξ σ) (E : Submodule ℂ (Space Ξ σ))
    (hE : IsTranslationStable ht E) (hA : A ≤ Subgroup.center Γ)
    (muA : Measure A) (χ : A →* ℂˣ), CentralIntegralConvergesOn E muA χ →
    ∀ (H : Subgroup Γ)
      (ha : IsAdmissible (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation),
      coefficientFunctionSpace
          (SmoothRep.of (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation
            ha.1) ≤
        schwartzCentralIntegralSpan E muA χ

theorem projectedCoefficientClosure : ProjectedCoefficientClosureStatement.{uG} :=
  fun _ _ _ _ _ _ _ _ _ ht E hE hA muA χ hc H ha =>
    coefficientFunctionSpace_projectedLeftSubrepresentation_le ht E hE hA muA χ hc H ha

end Langlands.HarishChandraSchwartz
