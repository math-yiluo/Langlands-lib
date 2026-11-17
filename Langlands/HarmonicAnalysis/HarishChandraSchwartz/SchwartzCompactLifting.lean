import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Jacquet.BlockCompressionProof

/-! # Compact lifting through the central integral

The smooth two-sided translation action permits normalized finite-orbit averaging.
This gives an actual bi-invariant preimage, provided the defining central integrals
on the translation-stable subspace converge.
-/

noncomputable section

universe uG

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

section Equivariance

variable {Γ : Type uG} [Group Γ] [MeasurableSpace Γ]
  {A : Subgroup Γ} [MeasurableSpace A]

omit [MeasurableSpace Γ] in
/-- The raw central integral commutes with both translations. No exchange of
integrals or normalization of the central measure occurs here. -/
theorem centralProjection_translate (hA : A ≤ Subgroup.center Γ)
    (muA : Measure A) (χ : A →* ℂˣ) (g₁ g₂ : Γ) (f : Γ → ℂ) :
    centralProjection muA χ (translate g₁ g₂ f) =
      translate g₁ g₂ (centralProjection muA χ f) := by
  funext x
  apply integral_congr_ae
  filter_upwards [] with a
  congr 1
  have hc : g₂⁻¹ * (a : Γ) = (a : Γ) * g₂⁻¹ :=
    Subgroup.mem_center_iff.mp (hA a.property) g₂⁻¹
  change f (g₂⁻¹ * ((a : Γ) * x) * g₁) = f ((a : Γ) * (g₂⁻¹ * x * g₁))
  congr 1
  calc
    g₂⁻¹ * ((a : Γ) * x) * g₁ = (g₂⁻¹ * (a : Γ)) * (x * g₁) := by group
    _ = ((a : Γ) * g₂⁻¹) * (x * g₁) := by rw [hc]
    _ = (a : Γ) * (g₂⁻¹ * x * g₁) := by group

/-- The all-translates integrable cuspidal kernel is stable under translations. -/
theorem IsIntegrableUnipotentCuspidal.translate {U : Subgroup Γ}
    {muU : Measure U} {f : Γ → ℂ} (hf : IsIntegrableUnipotentCuspidal muU f)
    (g₁ g₂ : Γ) : IsIntegrableUnipotentCuspidal muU (translate g₁ g₂ f) := by
  intro x y
  simpa only [translate_apply, mul_assoc] using hf (g₂⁻¹ * x) (y * g₁)

end Equivariance

section TranslationRepresentation

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {Ξ σ : Γ → ℝ}

/-- The actual two-sided action on the Schwartz space, by `f(x) ↦ f(g₂⁻¹ x g₁)`. -/
def Space.translationRepresentation (ht : TranslationWeights Ξ σ) :
    Representation ℂ (Γ × Γ) (Space Ξ σ) where
  toFun g := Space.translateLinear ht g.1 g.2
  map_one' := by
    apply LinearMap.ext
    intro f
    exact Space.translate_one_one ht f
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    exact (Space.translate_translate ht g.1 g.2 h.1 h.2 f).symm

@[simp] theorem Space.translationRepresentation_apply (ht : TranslationWeights Ξ σ)
    (g : Γ × Γ) (f : Space Ξ σ) (x : Γ) :
    Space.translationRepresentation ht g f x = f (g.2⁻¹ * x * g.1) := rfl

/-- Every Schwartz vector has an open two-sided stabilizer. -/
theorem Space.isSmooth_translationRepresentation [Nonempty (CompactOpenSubgroup Γ)]
    (ht : TranslationWeights Ξ σ) : IsSmooth (Space.translationRepresentation ht) := by
  intro f
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  refine ⟨K.1.prod K.1, ?_⟩
  intro g
  apply Space.ext
  intro x
  exact congrFun (hK.1.translate_eq g.property.1 g.property.2) x

/-- Stability of a Schwartz subspace under the actual two-sided action. -/
def IsTranslationStable (ht : TranslationWeights Ξ σ)
    (E : Submodule ℂ (Space Ξ σ)) : Prop :=
  ∀ g₁ g₂ : Γ, ∀ f ∈ E, Space.translate ht g₁ g₂ f ∈ E

/-- A stable subspace with its actual two-sided translation representation. -/
def translationSubrepresentation (ht : TranslationWeights Ξ σ)
    (E : Submodule ℂ (Space Ξ σ)) (hE : IsTranslationStable ht E) :
    Subrepresentation (Space.translationRepresentation ht) where
  toSubmodule := E
  apply_mem_toSubmodule g := hE g.1 g.2

/-- Smoothness passes to a translation-stable subspace. -/
theorem isSmooth_translationSubrepresentation [Nonempty (CompactOpenSubgroup Γ)]
    (ht : TranslationWeights Ξ σ) (E : Submodule ℂ (Space Ξ σ))
    (hE : IsTranslationStable ht E) :
    IsSmooth (translationSubrepresentation ht E hE).toRepresentation := by
  intro f
  obtain ⟨K, hK⟩ := Space.isSmooth_translationRepresentation ht f.val
  refine ⟨K, ?_⟩
  intro k
  exact Subtype.ext (hK k)

end TranslationRepresentation

section CompactLifting

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Nonempty (CompactOpenSubgroup Γ)]
  {Ξ σ : Γ → ℝ} {A : Subgroup Γ} [MeasurableSpace A]

/-- Compact averaging lifts a bi-invariant element of the raw full image to a
bi-invariant Schwartz vector in the same subspace. -/
theorem exists_biInvariant_central_preimage (ht : TranslationWeights Ξ σ)
    (E : Submodule ℂ (Space Ξ σ)) (hE : IsTranslationStable ht E)
    (hA : A ≤ Subgroup.center Γ) (muA : Measure A) (χ : A →* ℂˣ)
    (hc : CentralIntegralConvergesOn E muA χ)
    (H : OpenSubgroup Γ) (hH : IsCompact (H : Set Γ))
    {f : Γ → ℂ} (hf : f ∈ schwartzCentralIntegralImage E muA χ)
    (hHf : IsBiInvariant H.toSubgroup f) :
    ∃ φ : Space Ξ σ, φ ∈ E ∧ IsBiInvariant H.toSubgroup (φ : Γ → ℂ) ∧
      centralProjection muA χ φ = f := by
  obtain ⟨φ, hφ, hφf⟩ := hf
  let τ := (translationSubrepresentation ht E hE).toRepresentation
  have hτ : IsSmooth τ := isSmooth_translationSubrepresentation ht E hE
  have hHH : IsCompact (H.prod H : Set (Γ × Γ)) := hH.prod hH
  let v : E := ⟨φ, hφ⟩
  let w : E := Compact.averageMap τ hτ (H.prod H) hHH v
  have hw := Compact.averageMap_mem_fixedVectors τ hτ (H.prod H) hHH v
  refine ⟨w.val, w.property, ?_, ?_⟩
  · intro h₁ hh₁ h₂ hh₂ x
    have h := hw ⟨(h₂, h₁⁻¹), hh₂, H.inv_mem hh₁⟩
    change τ (h₂, h₁⁻¹) w = w at h
    have he := congrArg (fun z : E => (z.val : Γ → ℂ) x) h
    change (w.val : Γ → ℂ) ((h₁⁻¹)⁻¹ * x * h₂) = (w.val : Γ → ℂ) x at he
    simpa only [inv_inv] using he
  · change centralIntegralOn E muA χ hc w = f
    apply Jacquet.map_averageMap_of_forall_eq τ hτ (H.prod H) hHH
      (centralIntegralOn E muA χ hc) v f
    intro k
    change centralProjection muA χ (translate k.val.1 k.val.2 (φ : Γ → ℂ)) = f
    rw [centralProjection_translate hA, hφf]
    exact hHf.translate_eq k.property.1 k.property.2

end CompactLifting

end Langlands.HarishChandraSchwartz
