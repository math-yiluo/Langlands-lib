import Langlands.BaseChange.Norm
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.ClassFieldTheory.Local.UniverseZero.UniverseZeroModel

/-! # Intertwining diagonals of distinct orders -/

noncomputable section

namespace Langlands.BaseChange

open Matrix
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)

universe v

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{v} p)
  {n : ℕ} (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)

local notation "D" => E.canonicalTopologicalData

/-- When the two diagonals have the same coordinate orders and the orders
are distinct, a twisted intertwiner must be diagonal. -/
theorem exists_diagonalUnits_of_strict_twistedConj {a b : Fin n → E.Carrierˣ}
    (hOrd : ∀ i, (D).ord (a i : E.Carrier) = (D).ord (b i : E.Carrier))
    (hDistinct : Function.Injective (fun i => (D).ord (a i : E.Carrier)))
    {x : GeneralLinear n E.Carrier}
    (hx : x⁻¹ * diagonalUnits a * entrywiseAut τ n x = diagonalUnits b) :
    ∃ t : Fin n → E.Carrierˣ, x = diagonalUnits t := by
  classical
  have hmul : diagonalUnits a * entrywiseAut τ n x = x * diagonalUnits b := by
    calc
      _ = x * (x⁻¹ * diagonalUnits a * entrywiseAut τ n x) := by group
      _ = _ := congrArg (x * ·) hx
  have hentry (i j : Fin n) : (a i : E.Carrier) * τ (x i j) = x i j * (b j : E.Carrier) := by
    have he := congrArg (fun z : GeneralLinear n E.Carrier => z i j) hmul
    change ((diagonalUnits a).val * (x.val.map τ.toRingHom)) i j =
      (x.val * (diagonalUnits b).val) i j at he
    simp only [diagonalUnits_val, diagonal_mul, mul_diagonal, Matrix.map_apply] at he
    exact he
  have hOff (i j : Fin n) (hij : i ≠ j) : x i j = 0 := by
    by_contra hz
    have hv := congrArg (D).ord (hentry i j)
    rw [(D).ord_mul (a i).ne_zero ((map_ne_zero τ).mpr hz),
      (D).ord_mul hz (b j).ne_zero, LocalClassField.UniverseZero.ord_eq_of_algEquiv τ D D,
      ← hOrd j, add_comm ((D).ord (x i j))] at hv
    exact hij (hDistinct (add_right_cancel hv))
  have hxdiag : x.val = diagonal (fun i => x i i) := by
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simp [h, hOff i j h]
  have hdiag (i : Fin n) : x i i ≠ 0 := by
    intro hi
    have hn : x.val.det ≠ 0 := (GeneralLinear.determinant x).ne_zero
    rw [hxdiag, det_diagonal] at hn
    exact hn (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  refine ⟨fun i => Units.mk0 (x i i) (hdiag i), Units.ext ?_⟩
  rw [diagonalUnits_val]
  exact hxdiag

end Langlands.BaseChange
