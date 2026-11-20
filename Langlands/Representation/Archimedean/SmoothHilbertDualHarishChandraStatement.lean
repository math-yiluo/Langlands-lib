import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement
import Langlands.Representation.Archimedean.SmoothDualEvaluation

/-! # Compact-finite intertwiners into the inverse-transpose twisted continuous dual -/

noncomputable section

universe uH
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The continuous complex dual of a representation of actual `GL_n(F)`, twisted by the
published inverse-transpose automorphism: `g` acts on a functional `L` by
`L ↦ L ∘ R((g⁻¹)ᵀ)⁻¹ = L ∘ R(gᵀ)`. -/
def inverseTransposeDualRepresentation (F : Type) [RCLike F] (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : Langlands.GeneralLinear n F →* (E →L[ℂ] E)) :
    Langlands.GeneralLinear n F →* (StrongDual ℂ E →L[ℂ] StrongDual ℂ E) :=
  (continuousDualRepresentation R).comp
    (Langlands.GeneralLinear.inverseTranspose n F).toMonoidHom

/-- **Inverse-transpose dual Harish-Chandra intertwiner (real general linear groups).**
Let `R` be a jointly continuous, topologically irreducible and compact admissible
representation of actual `GL_(r+1)(ℝ)` on a complete complex Hilbert space, and let
`(ρ, π)` be an irreducible admissible `(𝔤𝔩_(r+1)(ℝ), O(r+1))`-module structure on its
compact-finite genuine smooth vectors that is compatible with the actual orthogonal
action and genuine derivatives. Then there is a nonzero linear map from these vectors
into the genuine smooth vectors of the inverse-transpose twisted continuous dual that
intertwines the compact action and the derivatives. -/
def RealSmoothHilbertDualHarishChandraStatement : Prop :=
  ∀ (r : ℕ) (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Langlands.GeneralLinear (r + 1) ℝ →* (H →L[ℂ] H))
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ)
      (smoothHilbertKFinite ℝ (r + 1) R))
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆
      Module.End ℂ (smoothHilbertKFinite ℝ (r + 1) R)),
    IsIrreducibleAdmissibleHilbertRepresentation ℝ (r + 1) R →
    IsRealGKModule (r + 1) ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
    IsSmoothGKIntertwiner ℝ (r + 1) R ρ π (smoothHilbertKFinite ℝ (r + 1) R).subtype →
      ∃ f : smoothHilbertKFinite ℝ (r + 1) R →ₗ[ℂ]
          DerivativeSmoothVectors (matrixModel ℝ (r + 1))
            (inverseTransposeDualRepresentation ℝ (r + 1) R),
        f ≠ 0 ∧
          IsSmoothGKIntertwiner ℝ (r + 1) (inverseTransposeDualRepresentation ℝ (r + 1) R)
            ρ π f

end Langlands.Archimedean
