import Langlands.Representation.Geometric.IntersectionChamberCoordinates
import Langlands.Representation.Classification.MaximalConeExponents

/-! Numerical projection after an explicitly supplied fine-character extension. -/

noncomputable section

namespace Langlands.Geometric.ChamberProjection

open GeneralLinear Finset
open scoped BigOperators

private theorem sum_coordinateBlock {n : ℕ} (C : BlockShape n)
    (f : Fin n → ℝ) (j : Fin C.length) :
    (∑ a ∈ univ.filter (fun a => blockIndex C a = j), f a) =
      ∑ b : Fin (C.size j), f (C.index j b) := by
  classical
  rw [sum_filter, ← C.indexEquiv.sum_comp, Fintype.sum_sigma]
  simp only [BlockShape.blockIndex_indexEquiv]
  simp [BlockShape.index_eq_indexEquiv]

/-- Repeated diagonal values sum to the sum of fine scalar exponents over the
fine blocks assigned to the selected target block. -/
theorem diagonal_sum_eq_fibre_sum {n : ℕ} (D C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (q : Fin D.length → Fin C.length)
    (hq : ∀ a : Fin n, q (blockIndex D a) = blockIndex C (w a))
    (x : Fin D.length → ℝ) (j : Fin C.length) :
    (∑ b : Fin (C.size j),
      x (blockIndex D (w.symm (C.index j b))) /
        (D.size (blockIndex D (w.symm (C.index j b))) : ℝ)) =
      ∑ k ∈ univ.filter (fun k => q k = j), x k := by
  classical
  let f : Fin n → ℝ := fun a => x (blockIndex D a) / (D.size (blockIndex D a) : ℝ)
  calc
    _ = ∑ a ∈ univ.filter (fun a => blockIndex C a = j), f (w.symm a) :=
      (sum_coordinateBlock C (fun a => f (w.symm a)) j).symm
    _ = ∑ a ∈ univ.filter (fun a => q (blockIndex D a) = j), f a := by
      simp only [sum_filter]
      rw [← Equiv.sum_comp w
        (fun a => if blockIndex C a = j then f (w.symm a) else 0)]
      apply sum_congr rfl
      intro a _
      rw [← hq a, Equiv.symm_apply_apply]
    _ = ∑ k ∈ univ.filter (fun k => q k = j),
        (D.size k : ℝ) * (x k / (D.size k : ℝ)) :=
      D.sum_blockIndex (fun k => x k / (D.size k : ℝ)) (fun k => q k = j)
    _ = _ := by
      apply sum_congr rfl
      intro k _
      have hd : (D.size k : ℝ) ≠ 0 := by exact_mod_cast (D.positive k).ne'
      exact mul_div_cancel₀ (x k) hd

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)

/-- The existing real-part fibre formula applies to the chamber pullback with
no monotonicity, minimality or rank hypothesis. -/
theorem chamberRestriction_isRealPartOf
    {ψ : (Fin (B.flatten S).length → F.Carrierˣ) →* ℂˣ}
    {x : Fin (B.flatten S).length → ℝ} (hx : T.IsRealPartOf ψ x) :
    T.IsRealPartOf (ψ.comp (chamberRestriction B C w S F.Carrier))
      (fun j => ∑ k ∈ univ.filter (fun k => chamberIndex B C w S k = j), x k) := by
  apply T.isRealPartOf_coarsen (q := chamberIndex B C w S) hx (fun _ => rfl) _
  intro _
  rfl

/-- Once an actual extended fine character has been supplied, the real part of
its coarse restriction is exactly the inverse-permuted diagonal block sum. -/
theorem diagonal_projection_of_character_extension
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    {ψ : (Fin (B.flatten S).length → F.Carrierˣ) →* ℂˣ}
    {χ : (Fin C.length → F.Carrierˣ) →* ℂˣ}
    {x : Fin (B.flatten S).length → ℝ} {y : Fin C.length → ℝ}
    (hx : T.IsRealPartOf ψ x) (hy : T.IsRealPartOf χ y)
    (hext : ψ.comp (chamberRestriction B C w S F.Carrier) = χ)
    (j : Fin C.length) :
    (∑ b : Fin (C.size j),
      x (blockIndex (B.flatten S) (w.symm (C.index j b))) /
        ((B.flatten S).size (blockIndex (B.flatten S) (w.symm (C.index j b))) : ℝ)) =
      y j := by
  have hreal := chamberRestriction_isRealPartOf T B C w S hx
  rw [hext] at hreal
  have hcoord := congrFun (hreal.eq hy) j
  rw [diagonal_sum_eq_fibre_sum (B.flatten S) C w (chamberIndex B C w S)
    (chamberIndex_blockIndex B C w S hS) x j]
  exact hcoord

end Langlands.Geometric.ChamberProjection
