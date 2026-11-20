import Langlands.Representation.Archimedean.SmoothHilbert
import Langlands.Representation.Archimedean.GKModule

/-! # Casselman–Wallach extension of compact-finite intertwiners to genuine smooth vectors -/

noncomputable section

universe uV uE uE₁ uE₂
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section Banach

variable (F : Type) [RCLike F] (n : ℕ)
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Langlands.GeneralLinear n F →* (E →L[ℂ] E))

/-- Compact-finite vectors in the genuine smooth carrier of a representation on a complex
normed space: those whose orbit under the actual orthogonal or unitary group spans a
finite-dimensional space. On a Hilbert space this is the same submodule as
`smoothHilbertKFinite`. -/
def smoothKFinite : Submodule ℂ (DerivativeSmoothVectors (matrixModel F n) R) :=
  (FiniteVectors.subrepresentation
    ((DerivativeSmoothVectors.representation (matrixModel F n) R).comp
      Unitary.toUnits)).toSubmodule

/-- A linear map from an algebraic module into the genuine smooth carrier that
intertwines the compact action with the actual orthogonal or unitary action and each
complexified real matrix direction `1 ⊗ X` with the genuine derivative along `X`. -/
def IsSmoothGKIntertwiner {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (f : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) R) : Prop :=
  (∀ (k : Matrix.unitaryGroup (Fin n) F) (v : V),
    f (ρ k v) = DerivativeSmoothVectors.representation (matrixModel F n) R
      (Unitary.toUnits k) (f v)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) F) (v : V),
    f (π (1 ⊗ₜ[ℝ] X) v) = DerivativeSmoothVectors.operator (matrixModel F n) R X (f v)

end Banach

/-- **Casselman–Wallach extension (real general linear groups).** Let `V` be an
irreducible admissible `(𝔤, K)`-module for `GL_(r+1)(ℝ)` and `O(r+1)`. Suppose that a
linear equivalence `e` identifies `V`, with its compact action and derivatives, with all
compact-finite genuine smooth vectors of a jointly continuous representation `R₁` on a
complex Banach space. Then every linear map `f` from `V` into the genuine smooth vectors
of any jointly continuous representation `R₂` on a complex Banach space that
intertwines the compact action and derivatives extends to a continuous linear map
between the genuine smooth carriers, with their word-derivative topologies, that is
equivariant for the actual group actions. -/
def RealSmoothCasselmanWallachExtensionStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E₁ : Type uE₁) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (R₁ : Langlands.GeneralLinear (r + 1) ℝ →* (E₁ →L[ℂ] E₁))
    (E₂ : Type uE₂) [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (R₂ : Langlands.GeneralLinear (r + 1) ℝ →* (E₂ →L[ℂ] E₂))
    (e : V ≃ₗ[ℂ] smoothKFinite ℝ (r + 1) R₁)
    (f : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₂),
    IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
    IsContinuousRepresentation R₁ → IsContinuousRepresentation R₂ →
    IsSmoothGKIntertwiner ℝ (r + 1) R₁ ρ π
      ((smoothKFinite ℝ (r + 1) R₁).subtype.comp e.toLinearMap) →
    IsSmoothGKIntertwiner ℝ (r + 1) R₂ ρ π f →
      ∃ T : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₁ →L[ℂ]
          DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₂,
        (∀ (g : Langlands.GeneralLinear (r + 1) ℝ)
            (y : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₁),
          T (DerivativeSmoothVectors.representation (matrixModel ℝ (r + 1)) R₁ g y) =
            DerivativeSmoothVectors.representation (matrixModel ℝ (r + 1)) R₂ g (T y)) ∧
        ∀ v : V, T (e v) = f v

end Langlands.Archimedean
