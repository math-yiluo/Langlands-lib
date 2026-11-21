import Langlands.Shimura.Unitary.RealReflex

/-!
# Harris reflex field at the prescribed complex embedding

Fix the distinguished real place before using the signatures to construct
charts. The CM section must also have the chosen orientation on the
imaginary quadratic subfield.
-/

universe u v w t

set_option autoImplicit false

open Algebra NumberField

namespace Langlands.Shimura

/-- A central simple unitary datum with the Harris signatures at the real
place below `e` and at all other places admits charts for the CM type cut
out by `e` on the imaginary quadratic subfield. The actual reflex field
for these charts is the image of `e`, including in rank two when the real
base has even degree. -/
def HarrisReflexAtEmbeddingStatement : Prop :=
  ∀ (E₀ : Type u) [Field E₀] [NumberField E₀] [IsTotallyReal E₀]
    (E : Type v) [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra E₀ E] [IsQuadraticExtension E₀ E]
    (K₀ : Type t) [Field K₀] [NumberField K₀] [IsCMField K₀] [IsQuadraticExtension ℚ K₀]
    (ι : K₀ →+* E) (e : E →+* ℂ) (n : ℕ)
    (A : Type w) [Ring A] [Algebra E A] [Algebra E₀ A] [IsScalarTower E₀ E A]
    [Algebra ℚ A] [IsScalarTower ℚ E₀ A] (D : CentralSimpleUnitaryData E₀ E A n),
    Even (Module.finrank ℚ E₀) →
    HasSignature D.toSecondKindInvolution (realPlaceBelow E₀ e) n (n - 1) →
    (∀ τ : E₀ →+* ℝ, τ ≠ realPlaceBelow E₀ e → HasSignature D.toSecondKindInvolution τ n n) →
    ∃ C : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E₀ ι (e.comp ι)),
      C.distinguished = realPlaceBelow E₀ e ∧
      C.distinguishedEmbedding = e ∧
      D.realReflexField C = e.toRatAlgHom.fieldRange

end Langlands.Shimura
