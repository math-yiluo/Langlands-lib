import Langlands.GroupScheme.GeneralLinearLocalization
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : Type u) [CommRing R]

/-- Specializing the universal polynomial matrix to the identity evaluates its
determinant to one. -/
theorem determinantPolynomial_eval_identity :
    aeval (fun p : n × n => (1 : Matrix n n R) p.1 p.2)
      (determinantPolynomial n R) = 1 := by
  let e : MatrixPolynomial n R →ₐ[R] R :=
    aeval (fun p : n × n => (1 : Matrix n n R) p.1 p.2)
  have h : e.mapMatrix (matrixVariables n R) = 1 := by
    ext i j
    simp [e, matrixVariables]
  change e (determinantPolynomial n R) = 1
  rw [determinantPolynomial, AlgHom.map_det, h, Matrix.det_one]

/-- The determinant polynomial is nonzero over any nontrivial coefficient ring. -/
theorem determinantPolynomial_ne_zero [Nontrivial R] :
    determinantPolynomial n R ≠ 0 := by
  intro h
  have he := determinantPolynomial_eval_identity n R
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- The two-matrix coordinate presentation of GL is a domain over a domain. -/
theorem coordinateRing_isDomain [IsDomain R] : IsDomain (CoordinateRing n R) := by
  let : IsDomain (DeterminantLocalization n R) :=
    Localization.Away.isDomain (determinantPolynomial_ne_zero n R)
  exact (determinantLocalizationEquiv n R).toMulEquiv.isDomain

/-- The GL coordinate algebra inherits the domain property of its coefficients. -/
instance coordinateRingIsDomain [IsDomain R] : IsDomain (CoordinateRing n R) :=
  coordinateRing_isDomain n R

/-- The function field used to test a character on the generic invertible matrix. -/
abbrev CharacterFunctionField [IsDomain R] := FractionRing (CoordinateRing n R)

/-- The generic invertible matrix over the function field of GL. -/
def characterGenericPoint [IsDomain R] : GL n (CharacterFunctionField n R) :=
  Matrix.GeneralLinearGroup.map
    (algebraMap (CoordinateRing n R) (CharacterFunctionField n R)) (universal n R)

@[simp] theorem characterGenericPoint_apply [IsDomain R] (i j : n) :
    characterGenericPoint n R i j =
      algebraMap (CoordinateRing n R) (CharacterFunctionField n R)
        (universal n R i j) := rfl

/-- Passing to the generic field loses no equality in the coordinate ring. -/
theorem characterFunctionField_injective [IsDomain R] :
    Function.Injective (algebraMap (CoordinateRing n R) (CharacterFunctionField n R)) :=
  IsFractionRing.injective _ _

end Langlands.GroupScheme.GeneralLinear
