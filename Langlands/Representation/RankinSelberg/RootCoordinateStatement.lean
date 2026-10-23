import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.Whittaker.Iwasawa

/-! The cumulative-product torus coordinates in the equal-rank JPSS integral. -/

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear
open scoped BigOperators

universe uF

/-- The coordinate change from simple-root and final coordinates to diagonal
entries is a continuous group automorphism preserving the actual product Haar
measure. The remaining identities give its roots, determinant, last row and
upper-Borel modulus. This is a proposition target, not an asserted theorem. -/
def RootCoordinateChangeStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : MeasurableSpace F.Carrierˣ := borel F.Carrierˣ
  letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let A := Fin (n + 1) → F.Carrierˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let toRoots : A → A := fun b =>
    Fin.lastCases (b (Fin.last n)) (fun i => b i.castSucc / b i.succ)
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  Continuous toDiagonal ∧ Continuous toRoots ∧
    Function.LeftInverse toRoots toDiagonal ∧
    Function.RightInverse toRoots toDiagonal ∧
    (∀ a b, toDiagonal (a * b) = toDiagonal a * toDiagonal b) ∧
    Measure.map toDiagonal dA = dA ∧
    ∀ a : A,
      (∀ i : Fin n, toDiagonal a i.castSucc / toDiagonal a i.succ = a i.castSucc) ∧
      toDiagonal a (Fin.last n) = a (Fin.last n) ∧
      Matrix.det (Iwasawa.diagonalUnits (toDiagonal a)).val =
        ∏ i, (a i : F.Carrier) ^ (i.val + 1) ∧
      (∀ k : Langlands.GeneralLinear (n + 1) F.Carrier,
        lastRow (Iwasawa.diagonalUnits (toDiagonal a) * k) =
          (a (Fin.last n) : F.Carrier) • lastRow k) ∧
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (i < ·),
        T.normalizedAbs ((toDiagonal a i / toDiagonal a j : F.Carrierˣ) : F.Carrier)) =
        ∏ i, T.normalizedAbs (a i : F.Carrier) ^ ((i.val + 1) * (n - i.val))

end Langlands.RankinSelberg
