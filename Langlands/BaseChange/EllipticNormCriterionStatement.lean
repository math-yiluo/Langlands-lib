import Langlands.BaseChange.Norm
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Norm.Basic

/-!
# The norm criterion for regular elliptic elements

The statement that, for a cyclic algebra `E` over a nonarchimedean local field `F` of
characteristic zero with generator `σ`, a regular elliptic element `γ` of `GL_n(F)` is a norm
from `GL_n(E)` exactly when `det γ` is a norm from `Eˣ` (Arthur–Clozel 1989, Chapter 1,
Lemma 1.4, printed p. 8, for a cyclic field extension). Statement only; not proved here. See the
paired Markdown.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

/-- For a nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` of group
`⟨σ⟩` of order `l`, `n : ℕ` and a regular elliptic `γ ∈ GL_n(F)`: `γ` is a norm from `GL_n(E)`
(`IsNorm σ l γ`) if and only if `det γ` lies in the image of the algebra norm `Eˣ → Fˣ`. -/
def EllipticNormCriterionStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    IsCyclicAlgebra σ l → ∀ γ : GeneralLinear n F, IsRegularElliptic γ →
      (IsNorm σ l γ ↔
        GeneralLinear.determinant γ ∈ (Units.map (Algebra.norm F : E →* F)).range)

end Langlands.BaseChange
