import Langlands.Global.ArchimedeanRealWordBounds
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Comparing actual real words with supplied orbit derivatives -/

noncomputable section

universe u v w u𝔤 uH uG

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] (n : ℕ)
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  (π : G →* (E →L[ℂ] E))
  (A : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V) (j : V →ₗ[ℂ] E)
  (ζ : RealLieAlgebra F n → 𝔤)
  (hgen : ∀ (X : RealLieAlgebra F n) (v : V),
    j (A (envelopingGenerator F n (complexify F n X)) v) =
      Langlands.Archimedean.lieDerivative I π (ζ X) (j v))

include hgen

/-- Compatibility on the original space identifies every real word with the
corresponding iterated orbit derivative. -/
theorem map_realEnvelopingWord_eq_iteratedLieDerivative
    (xs : List (RealLieAlgebra F n)) (v : V) :
    j (A (realEnvelopingWord F n xs) v) =
      Langlands.Archimedean.iteratedLieDerivative I π (xs.map ζ) (j v) := by
  induction xs with
  | nil => simp only [realEnvelopingWord_nil, map_one, Module.End.one_apply,
      List.map_nil, Langlands.Archimedean.iteratedLieDerivative_nil]
  | cons X xs ih =>
    simp only [realEnvelopingWord_cons, map_mul, Module.End.mul_apply, hgen,
      ih, List.map_cons, Langlands.Archimedean.iteratedLieDerivative_cons]

/-- A finite family of actual enveloping derivatives is bounded by finitely
many iterated orbit derivatives, assuming compatibility of the real generators.
The family and constant precede the original vector. -/
theorem sum_norm_enveloping_le_iteratedLieDerivatives
    (D : Finset (EnvelopingAlgebra F n)) :
    ∃ (S : Finset (List 𝔤)) (C : ℝ), 0 ≤ C ∧
      ∀ v : V, ∑ d ∈ D, ‖j (A d v)‖ ≤
        C * ∑ xs ∈ S, ‖Langlands.Archimedean.iteratedLieDerivative I π xs (j v)‖ := by
  classical
  obtain ⟨S, C, hC, hbound⟩ := sum_norm_enveloping_le_realWords F n A j D
  refine ⟨S.image (List.map ζ), C * (S.card : ℝ),
    mul_nonneg hC (Nat.cast_nonneg _), ?_⟩
  intro v
  let B : ℝ := ∑ xs ∈ S.image (List.map ζ),
    ‖Langlands.Archimedean.iteratedLieDerivative I π xs (j v)‖
  have hs : (∑ xs ∈ S, ‖j (A (realEnvelopingWord F n xs) v)‖) ≤
      (S.card : ℝ) * B := by
    calc
      _ ≤ ∑ _xs ∈ S, B := by
        apply Finset.sum_le_sum
        intro xs hxs
        rw [map_realEnvelopingWord_eq_iteratedLieDerivative F n I π A j ζ hgen]
        exact Finset.single_le_sum
          (f := fun ys => ‖Langlands.Archimedean.iteratedLieDerivative I π ys (j v)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_image.mpr ⟨xs, hxs, rfl⟩)
      _ = (S.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
  exact (hbound v).trans ((mul_le_mul_of_nonneg_left hs hC).trans_eq
    (mul_assoc C (S.card : ℝ) B).symm)

end Langlands.Global.ArchimedeanGL
