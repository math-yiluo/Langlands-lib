import Langlands.Representation.Unitary.CompactInductionConjugateStatement
import Langlands.Representation.Aubert.General.NormalizedInductionHermitianDuality
import Langlands.Representation.Induction.CompactQuotientProof

/-! # Pointwise conjugation of compact induced functions -/

noncomputable section

namespace Langlands.Renard.CompactRepresentation

open Induction

universe u v

/-- Pointwise conjugation identifies the conjugate of unnormalized compact induction
with compact induction of the conjugate on a compact quotient. -/
theorem compactInductionConjugate : CompactInductionConjugateStatement.{u, v} := by
  intro G _ _ _ _ _ _ H _ _ V _ _ ρ _
  let τ := ConjSpace.rep ρ
  let T := ConjSpace.equiv V
  have hT (h : H) (x : V) : T (ρ h x) = τ h (T x) := by
    change T (ρ h x) = ConjSpace.rep ρ h (T x)
    rw [ConjSpace.rep_apply, T.symm_apply_apply]
  let smoothConjugate := smoothFunctionsConjEquiv H T hT
  let compactConjugate : CompactFunctions H ρ ≃ₗ⋆[ℂ] CompactFunctions H τ :=
    { toFun f := ⟨smoothConjugate f.val, (isClosed_quotientSupport H τ _).isCompact⟩
      invFun f := ⟨smoothConjugate.symm f.val, (isClosed_quotientSupport H ρ _).isCompact⟩
      left_inv f := Subtype.ext (smoothConjugate.symm_apply_apply f.val)
      right_inv f := Subtype.ext (smoothConjugate.apply_symm_apply f.val)
      map_add' f f' := Subtype.ext (smoothConjugate.map_add f.val f'.val)
      map_smul' z f := Subtype.ext (smoothConjugate.map_smulₛₗ z f.val) }
  let comparison := (ConjSpace.equiv (CompactFunctions H ρ)).symm.trans compactConjugate
  refine ⟨Representation.Equiv.mk comparison (fun g => ?_), fun f x => ?_⟩
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl
  · rfl

end Langlands.Renard.CompactRepresentation
