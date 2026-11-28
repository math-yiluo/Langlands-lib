import Langlands.BaseChange.TwistedCharacter.OpenCoset
import Langlands.HarmonicAnalysis.Distribution.TestPushforward
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct

/-! # Restricting the source and extending the target of a test pushforward -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Set Function _root_.Topology

section Extension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  {j : X → Y} (hj : IsOpenEmbedding j)

/-- Test transport along an open embedding, as a linear map. -/
def openEmbeddingTestExtension : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y :=
  (SchwartzBruhat.extendZero hj.isOpen_range).comp
    (Hecke.TestFunction.pullback hj.isEmbedding.toHomeomorph.symm).toLinearMap

@[simp]
theorem openEmbeddingTestExtension_apply (f : SchwartzBruhat X) (x : X) :
    openEmbeddingTestExtension hj f (j x) = f x :=
  extendAlongOpenEmbedding_apply hj f x

/-- The extension vanishes outside the image of the embedding. -/
theorem openEmbeddingTestExtension_apply_of_not_mem (f : SchwartzBruhat X) {y : Y}
    (hy : y ∉ range j) : openEmbeddingTestExtension hj f y = 0 :=
  SchwartzBruhat.extendZero_apply_of_not_mem hj.isOpen_range _ hy

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

private theorem integral_openEmbeddingTestExtension_mul (μ : Measure Y)
    (f : SchwartzBruhat X) (g : Y → ℂ) :
    (∫ y, openEmbeddingTestExtension hj f y * g y ∂μ) =
      ∫ x, f x * g (j x) ∂(μ.comap j) := by
  let e := hj.measurableEmbedding
  calc
    _ = ∫ y in range j, openEmbeddingTestExtension hj f y * g y ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      change SchwartzBruhat.extendZero hj.isOpen_range _ y * g y = 0
      rw [SchwartzBruhat.extendZero_apply_of_not_mem _ _ hy, zero_mul]
    _ = _ := by
      rw [← e.map_comap, e.integral_map]
      simp only [openEmbeddingTestExtension_apply]

end Extension

section Tensor

variable {X₁ X₂ Y₁ Y₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace X₂]
  [TopologicalSpace Y₁] [TopologicalSpace Y₂] [T2Space Y₁] [T2Space Y₂]

/-- Extending a tensor test along a product embedding extends each factor. -/
theorem openEmbeddingTestExtension_tensor {i : X₁ → Y₁} {j : X₂ → Y₂}
    (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
    (f : SchwartzBruhat X₁) (g : SchwartzBruhat X₂) :
    openEmbeddingTestExtension (hi.prodMap hj) (SchwartzBruhat.tensor f g) =
      SchwartzBruhat.tensor (openEmbeddingTestExtension hi f) (openEmbeddingTestExtension hj g) := by
  apply Hecke.TestFunction.ext
  rintro ⟨y, z⟩
  rw [SchwartzBruhat.tensor_apply]
  by_cases hy : y ∈ range i
  · by_cases hz : z ∈ range j
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨w, rfl⟩ := hz
      change openEmbeddingTestExtension (hi.prodMap hj) _ (Prod.map i j (x, w)) = _
      rw [openEmbeddingTestExtension_apply, openEmbeddingTestExtension_apply,
        openEmbeddingTestExtension_apply, SchwartzBruhat.tensor_apply]
    · have h : (y, z) ∉ range (Prod.map i j) := fun ⟨p, hp⟩ => hz ⟨p.2, congrArg Prod.snd hp⟩
      rw [openEmbeddingTestExtension_apply_of_not_mem _ _ h,
        openEmbeddingTestExtension_apply_of_not_mem _ _ hz, mul_zero]
  · have h : (y, z) ∉ range (Prod.map i j) := fun ⟨p, hp⟩ => hy ⟨p.1, congrArg Prod.fst hp⟩
    rw [openEmbeddingTestExtension_apply_of_not_mem _ _ h,
      openEmbeddingTestExtension_apply_of_not_mem _ _ hy, zero_mul]

end Tensor

section Pushforward

variable {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y] [TopologicalSpace Y'] [T2Space X] [T2Space Y']
  [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Y']

/-- A test pushforward restricts along an open source embedding and extends
along a target embedding with clopen image, with the matching pulled-back measures. -/
def EmbeddedTestPushforwardStatement [BorelSpace X] [BorelSpace X'] [BorelSpace Y] [BorelSpace Y']
    {i : X' → X} (hi : IsOpenEmbedding i) {j : Y → Y'} (hj : IsOpenEmbedding j)
    (μ : Measure X) (ν : Measure Y') (p : X → Y)
    (P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y) : Prop :=
  IsClosed (range j) → SchwartzBruhat.IsTestPushforward μ (ν.comap j) p P →
  SchwartzBruhat.IsTestPushforward (μ.comap i) ν (j ∘ p ∘ i)
    ((openEmbeddingTestExtension hj).comp (P.comp (openEmbeddingTestExtension hi)))

variable [BorelSpace X] [BorelSpace X'] [BorelSpace Y] [BorelSpace Y']

theorem embeddedTestPushforward {i : X' → X} (hi : IsOpenEmbedding i) {j : Y → Y'}
    (hj : IsOpenEmbedding j) (μ : Measure X) (ν : Measure Y') (p : X → Y)
    (P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y) :
    EmbeddedTestPushforwardStatement hi hj μ ν p P := by
  intro hC hP f g
  let g₀ := Hecke.TestFunction.pullback hj.isEmbedding.toHomeomorph
    (SchwartzBruhat.restrictClosed hC g)
  have hg (y : Y) : g₀ y = g (j y) := rfl
  calc
    _ = ∫ y, P (openEmbeddingTestExtension hi f) y * g (j y) ∂(ν.comap j) :=
      integral_openEmbeddingTestExtension_mul hj ν _ g
    _ = ∫ y, P (openEmbeddingTestExtension hi f) y * g₀ y ∂(ν.comap j) := by
      simp_rw [hg]
    _ = ∫ x, openEmbeddingTestExtension hi f x * g₀ (p x) ∂μ := hP _ _
    _ = _ := by
      rw [integral_openEmbeddingTestExtension_mul hi]
      simp_rw [hg, Function.comp_apply]

end Pushforward

end Langlands.BaseChange
