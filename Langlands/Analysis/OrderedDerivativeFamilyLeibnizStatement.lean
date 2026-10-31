import Langlands.Analysis.OrderedDerivativeFamilyNorm

/-! # A binomial Leibniz bound for complete ordered derivative families -/

noncomputable section
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

universe uA uI uJ uE uF uG uH

variable {A : Type uA} [Fintype A]
  {I : Type uI} [Fintype I] {J : Type uJ} [Fintype J]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- An exact binomial bound for the complete ordered derivative tensor of a
bilinear product, jointly over two finite families. -/
def OrderedDerivativeFamilyLeibnizStatement
    (v : A → E) (B : F →L[ℝ] G →L[ℝ] H) : Prop :=
  ∀ (p : ℕ) (f : I → E → F) (g : J → E → G) (S : Set E), IsOpen S →
    (∀ i, ContDiffOn ℝ ∞ (f i) S) → (∀ j, ContDiffOn ℝ ∞ (g j) S) →
    ∀ x ∈ S,
      orderedDerivativeFamilyNorm v p
          (fun ij : I × J => fun y => B (f ij.1 y) (g ij.2 y)) x ≤
        ‖B‖ * ∑ l ∈ Finset.range (p + 1), (p.choose l : ℝ) *
          orderedDerivativeFamilyNorm v l f x *
          orderedDerivativeFamilyNorm v (p - l) g x

end Langlands.Analysis
