import Langlands.Representation.RankinSelberg.RootCoordinateStatement
import Langlands.AllField.Group.GL.Padic
/-! The cumulative-product torus coordinates in the equal-rank JPSS integral. -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding RootCoordinateChangeStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear
open scoped BigOperators

universe uF

/-- The coordinate change from simple-root and final coordinates to diagonal
entries is a continuous group automorphism preserving the actual product Haar
measure. The remaining identities give its roots, determinant, last row and
upper-Borel modulus. This is a proposition target, not an asserted theorem. -/
def RootCoordinateChangeStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : MeasurableSpace Fˣ := borel Fˣ
  letI : BorelSpace Fˣ := ⟨rfl⟩
  let A := Fin (n + 1) → Fˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let toRoots : A → A := fun b =>
    Fin.lastCases (b (Fin.last n)) (fun i => b i.castSucc / b i.succ)
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
  Continuous toDiagonal ∧ Continuous toRoots ∧
    Function.LeftInverse toRoots toDiagonal ∧
    Function.RightInverse toRoots toDiagonal ∧
    (∀ a b, toDiagonal (a * b) = toDiagonal a * toDiagonal b) ∧
    Measure.map toDiagonal dA = dA ∧
    ∀ a : A,
      (∀ i : Fin n, toDiagonal a i.castSucc / toDiagonal a i.succ = a i.castSucc) ∧
      toDiagonal a (Fin.last n) = a (Fin.last n) ∧
      Matrix.det (Iwasawa.diagonalUnits (toDiagonal a)).val =
        ∏ i, (a i : F) ^ (i.val + 1) ∧
      (∀ k : Langlands.GeneralLinear (n + 1) F,
        lastRow (Iwasawa.diagonalUnits (toDiagonal a) * k) =
          (a (Fin.last n) : F) • lastRow k) ∧
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (i < ·),
        T.normalizedAbs ((toDiagonal a i / toDiagonal a j : Fˣ) : F)) =
        ∏ i, T.normalizedAbs (a i : F) ^ ((i.val + 1) * (n - i.val))

end Langlands.AllField.RankinSelberg
