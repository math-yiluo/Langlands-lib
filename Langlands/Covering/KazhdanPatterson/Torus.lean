import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.Algebra.BigOperators.Pi

/-! # The Kazhdan–Patterson bilinear pairing on the diagonal torus -/

namespace Langlands.KazhdanPatterson

open scoped BigOperators

universe u v

variable {r : ℕ} {U : Type u} {A : Type v} [CommGroup U] [CommGroup A]

/-- The determinant on the diagonal torus, given by the product of the entries. -/
def diagonalDeterminant : (Fin r → U) →* U where
  toFun t := ∏ i, t i
  map_one' := by simp
  map_mul' t s := Finset.prod_mul_distrib

@[simp]
theorem diagonalDeterminant_apply (t : Fin r → U) :
    diagonalDeterminant t = ∏ i, t i := rfl

@[simp]
theorem determinant_diagonalUnits {F : Type u} [Field F] (t : Fin r → Fˣ) :
    GeneralLinear.determinant (GeneralLinear.Iwasawa.diagonalUnits t) = diagonalDeterminant t :=
  GeneralLinear.Iwasawa.det_diagonalUnits t

private def pullbackPairing (H : U →* U →* A) (f g : (Fin r → U) →* U) :
    (Fin r → U) →* (Fin r → U) →* A :=
  ((MonoidHom.compHom' g).comp H).comp f

/-- The twisted torus pairing, with one symbol factor for each ordered pair `i < j`. -/
def torusPairing (H : U →* U →* A) (c : ℤ) : (Fin r → U) →* (Fin r → U) →* A :=
  (∏ ij ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun ij => ij.1 < ij.2),
    pullbackPairing H (Pi.evalMonoidHom _ ij.1) (Pi.evalMonoidHom _ ij.2)) *
      pullbackPairing H diagonalDeterminant diagonalDeterminant ^ c

@[simp]
theorem torusPairing_apply (H : U →* U →* A) (c : ℤ) (t s : Fin r → U) :
    torusPairing H c t s =
      (∏ ij ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun ij => ij.1 < ij.2),
        H (t ij.1) (s ij.2)) * H (∏ i, t i) (∏ i, s i) ^ c := by
  simp only [torusPairing, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.finsetProd_apply]
  rfl

end Langlands.KazhdanPatterson
