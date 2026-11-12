import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Mathlib.CategoryTheory.MorphismProperty.Representable

/-! # Diagonal properties of products and pullbacks -/

noncomputable section

universe v w

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.PullbackDiagonals

variable {C : Type w} [Category.{v} C] [HasPullbacks C]
  [HasBinaryProducts C] [HasTerminal C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

omit [P.IsMultiplicative] in
/-- Convert the binary-product diagonal to the relative diagonal over the terminal object. -/
theorem terminal_iff (X : C) : P.diagonal (terminal.from X) ↔ P (diag X) := by
  have h : pullback.diagonal (terminal.from X) = diag X ≫ (prodIsoPullback X X).hom := by
    apply pullback.hom_ext <;> simp [pullback.diagonal, pullback.lift_fst, pullback.lift_snd]
  rw [MorphismProperty.diagonal_iff, h, P.cancel_right_of_respectsIso]

/-- The diagonal of a product has every multiplicative, base-change-stable property
shared by its two factor diagonals. -/
theorem prod {X Y : C} (hX : P (diag X)) (hY : P (diag Y)) : P (diag (X ⨯ Y)) := by
  apply (terminal_iff P (X ⨯ Y)).mp
  have h₁ : P.diagonal (Limits.prod.fst : X ⨯ Y ⟶ X) :=
    P.diagonal.of_isPullback (IsPullback.of_hasBinaryProduct' X Y).flip
      ((terminal_iff P Y).mpr hY)
  have h₂ := P.diagonal.comp_mem _ _ h₁ ((terminal_iff P X).mpr hX)
  simpa using h₂

/-- A monomorphism preserves every such property of the ambient diagonal. -/
theorem of_mono {X Y : C} (i : X ⟶ Y) [Mono i] (hY : P (diag Y)) : P (diag X) := by
  apply (terminal_iff P X).mp
  have hi : P.diagonal i := P.of_isIso (pullback.diagonal i)
  have h := P.diagonal.comp_mem i (terminal.from Y) hi ((terminal_iff P Y).mpr hY)
  simpa using h

/-- Diagonal properties of the two sources pass to their arbitrary fibre product. -/
theorem pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : P (diag X)) (hY : P (diag Y)) : P (diag (Limits.pullback f g)) := by
  let i : Limits.pullback f g ⟶ X ⨯ Y :=
    Limits.prod.lift (Limits.pullback.fst f g) (Limits.pullback.snd f g)
  have : Mono i := by
    constructor
    intro T a b hab
    apply Limits.pullback.hom_ext
    · simpa [i] using congrArg (fun k => k ≫ Limits.prod.fst) hab
    · simpa [i] using congrArg (fun k => k ≫ Limits.prod.snd) hab
  exact of_mono P i (prod P hX hY)

end Langlands.AlgebraicGeometry.AlgebraicSpace.PullbackDiagonals
