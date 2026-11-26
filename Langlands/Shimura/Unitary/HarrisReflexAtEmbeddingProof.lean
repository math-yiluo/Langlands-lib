import Langlands.Shimura.Unitary.HarrisReflexAtEmbeddingStatement
import Langlands.Global.RealTensorSplitting

/-!
# Harris reflex field at the prescribed complex embedding: proof

The signature charts are built with the distinguished real place fixed in
advance, at the real place below the prescribed complex embedding `e`.
Harris's CM section then takes the value `e` there, and the reflex-field
calculation of `Langlands.Shimura.Unitary.RealReflex` applies because a
totally real field of even degree has a second real place.
-/

noncomputable section

universe u v w t

set_option autoImplicit false

open Algebra NumberField
open scoped TensorProduct

namespace Langlands.Shimura

namespace HarrisSignatureCharts

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  {σ : SecondKindInvolution E K A} {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}

/-- Charts at a prescribed distinguished real place `τ₁`: signature `(n - 1, 1)`
at `τ₁` and `(n, 0)` at every other real place, each chart chosen complex
linear for the CM section `Φ`. -/
def ofSignatureAt (hn : 1 < n) (τ₁ : E →+* ℝ) (h₁ : HasSignature σ τ₁ n (n - 1))
    (hτ : ∀ τ : E →+* ℝ, τ ≠ τ₁ → HasSignature σ τ n n) (hΦ : IsCMSection E K Φ) :
    HarrisSignatureCharts σ n Φ := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hs : ∀ τ : E →+* ℝ, HasSignature σ τ n (if τ = τ₁ then n - 1 else n) := by
    intro τ
    by_cases he : τ = τ₁
    · subst he
      simpa using h₁
    · simpa [he] using hτ τ he
  have hc := fun τ => (hs τ).exists_centerCompatible (Φ τ) (hΦ τ)
  exact
    { rank_gt_one := hn
      distinguished := τ₁
      equiv := fun τ => (hc τ).choose
      compatible := fun τ => (hc τ).choose_spec.1
      center := fun τ => (hc τ).choose_spec.2 }

@[simp] theorem ofSignatureAt_distinguished (hn : 1 < n) (τ₁ : E →+* ℝ)
    (h₁ : HasSignature σ τ₁ n (n - 1))
    (hτ : ∀ τ : E →+* ℝ, τ ≠ τ₁ → HasSignature σ τ n n) (hΦ : IsCMSection E K Φ) :
    (ofSignatureAt hn τ₁ h₁ hτ hΦ).distinguished = τ₁ :=
  rfl

end HarrisSignatureCharts

/-- A totally real number field of even degree over `ℚ` has a real embedding
different from any given one. -/
theorem exists_realEmbedding_ne_of_even_finrank {E : Type u} [Field E] [NumberField E]
    [IsTotallyReal E] (hEven : Even (Module.finrank ℚ E)) (τ₁ : E →+* ℝ) :
    ∃ τ : E →+* ℝ, τ ≠ τ₁ := by
  have hcard : Fintype.card (E →+* ℝ) = Module.finrank ℚ E :=
    (Fintype.card_congr (Global.TotallyReal.realComplexEmbeddings E)).trans
      (NumberField.Embeddings.card E ℂ)
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  obtain ⟨d, hd⟩ := hEven
  exact Fintype.exists_ne_of_one_lt_card (by omega) τ₁

/-- Harris's reflex-field identification at the prescribed complex embedding
`e`, including rank two. -/
theorem harrisReflexAtEmbedding : HarrisReflexAtEmbeddingStatement.{u, v, w, t} := by
  intro E₀ _ _ _ E _ _ _ _ _ K₀ _ _ _ _ ι e n A _ _ _ _ _ _ D hEven h₁ hτ
  let C : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E₀ ι (e.comp ι)) :=
    HarrisSignatureCharts.ofSignatureAt D.rank_gt_one (realPlaceBelow E₀ e) h₁ hτ
      (isCMSection_harrisCMSection E₀ ι (e.comp ι))
  have hd : C.distinguishedEmbedding = e :=
    ((eq_harrisCMSection_realPlaceBelow_iff (E := E₀) (ι := ι) (τ₀ := e.comp ι) e).mpr
      rfl).symm
  refine ⟨C, rfl, hd, ?_⟩
  rw [D.realReflexField_eq_distinguishedImage C
      (Or.inr (exists_realEmbedding_ne_of_even_finrank hEven C.distinguished)),
    HarrisSignatureCharts.distinguishedImage, hd]

end Langlands.Shimura
