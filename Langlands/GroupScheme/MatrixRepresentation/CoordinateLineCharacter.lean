import Langlands.GroupScheme.Chevalley.UnipotentLine
import Langlands.GroupScheme.Rational.Characters

/-! # The character of a stabilized coordinate line -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Every test point acts on the chosen coordinate vector by a global unit. -/
abbrev StabilizesCoordinateLine (ρ : MatrixRepresentation G n) (j : n) : Prop :=
  ρ.PreservesCoordinateLine j

variable (ρ : MatrixRepresentation G n) (j : n)
  (hline : ρ.StabilizesCoordinateLine j)

theorem coordinateLineScalar_unique (T : Over (Spec R)) (x : T ⟶ G.X)
    (a : Γ(T.left, ⊤)ˣ)
    (ha : (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      (a : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) : n → Γ(T.left, ⊤))) :
    ρ.coordinateLineScalar j hline T x = a := by
  apply Units.ext
  rw [ρ.coordinateLineScalar_val]
  have h := congrFun ha j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one] using h

/-- The same natural line action, with values in the represented multiplicative group. -/
def coordinateLinePoints (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (Gm (Spec R)).X) :=
  ρ.coordinateLineCharacterPoints j hline T

theorem coordinateLinePoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    ρ.coordinateLinePoints j hline T' (a ≫ x) =
      a ≫ ρ.coordinateLinePoints j hline T x :=
  ρ.coordinateLineCharacterPoints_naturality j hline a x

/-- The actual algebraic character induced on a stabilized coordinate line. -/
def coordinateLineRationalCharacter : rationalCharacters G :=
  Additive.ofMul (ρ.coordinateLineCharacter j hline)

theorem characterEval_coordinateLineCharacter (T : Over (Spec R)) (x : T ⟶ G.X) :
    characterEval (ρ.coordinateLineRationalCharacter j hline) T x =
      ρ.coordinateLineScalar j hline T x := by
  exact ρ.coordinateLineCharacter_scalar j hline T x

theorem coordinateLineCharacter_action (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      (characterEval (ρ.coordinateLineRationalCharacter j hline) T x : Γ(T.left, ⊤)) •
        (Pi.single j (1 : Γ(T.left, ⊤)) : n → Γ(T.left, ⊤)) := by
  rw [ρ.characterEval_coordinateLineCharacter]
  exact ρ.coordinateLineScalar_spec j hline T x

end Langlands.GroupScheme.MatrixRepresentation
