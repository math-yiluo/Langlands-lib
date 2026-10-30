import Langlands.Representation.Exponents.SupportedRegularWeylConeNumerics
import Langlands.Representation.Exponents.WeightedBlockCone
import Langlands.Representation.Exponents.PositiveRootParameterConeProof
import Langlands.Representation.Exponents.PositiveRootBlockSumsProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

/-! Weighted support parameters in full diagonal coordinates. -/

noncomputable section

namespace Langlands.SupportedRegularWeylComparison

open GeneralLinear Geometric Exponents RelativeRegularComparison Finset
open scoped BigOperators

set_option autoImplicit false

/-- Concatenating closed-cone vectors on consecutive blocks preserves the cone. -/
theorem closedCone_of_blockwise {n : ℕ} (B : BlockShape n)
    (x : Fin n → ℝ)
    (hx : ∀ i, IsClosedPositiveRootCone (fun a => x (B.index i a))) :
    IsClosedPositiveRootCone x := by
  apply (isClosedPositiveRootCone_iff_pairing x).mpr
  constructor
  · rw [← B.indexEquiv.sum_comp, Fintype.sum_sigma]
    exact Finset.sum_eq_zero fun i _ => (hx i).1
  · intro h hmono
    rw [← B.indexEquiv.sum_comp, Fintype.sum_sigma]
    apply Finset.sum_nonpos
    intro i _
    exact ((isClosedPositiveRootCone_iff_pairing _).mp (hx i)).2
      (fun a => h (B.index i a)) (hmono.comp (index_strictMono B i).monotone)

/-- The existing positive-root support parameter lies in the closed cone after
repeating each determinant exponent on its actual fine block. -/
theorem closedCone_of_positiveRootParameter {n : ℕ}
    (D : BlockShape n) (R : BlockRefinement D)
    (v : Fin (D.flatten R).length → ℝ)
    (hv : IsPositiveRootParameter D R v) :
    IsClosedPositiveRootCone (fun a => v (blockIndex (D.flatten R) a)) := by
  apply closedCone_of_blockwise D
  intro i
  have hweighted := ((positiveRootParameterCone n D R v).mp hv i).isClosedPositiveRootCone
  have hlocal := diagonal_cone_of_weighted_block_cone (R i)
    (fun k => v (D.flattenBlockEquiv R ⟨i, k⟩)) hweighted
  convert hlocal using 1
  funext a
  obtain ⟨⟨k, b⟩, rfl⟩ := (R i).indexEquiv.surjective a
  change v (blockIndex (D.flatten R) (D.index i ((R i).index k b))) =
    v (D.flattenBlockEquiv R ⟨i, blockIndex (R i) ((R i).index k b)⟩)
  rw [D.index_index_eq_flatten R ⟨i, k⟩ b, blockIndex_index, blockIndex_index]

/-- Transporting the fine presentation by its literal shape equality preserves
the full-diagonal cone. -/
theorem closedCone_of_transported_positiveRootParameter {n : ℕ}
    (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (v : Fin ((B.flatten Q).flatten R).length → ℝ)
    (hv : IsPositiveRootParameter (B.flatten Q) R v) :
    IsClosedPositiveRootCone (fun a => (h ▸ v) (blockIndex (B.flatten S) a)) := by
  simpa only [PositiveRootBlockSumsProof.transport_blockIndex] using
    closedCone_of_positiveRootParameter (B.flatten Q) R v hv

/-- A vector whose sum is zero on every coarse block is orthogonal to every
coarse-block-constant vector. -/
theorem block_pairing_zero {n : ℕ} (B : BlockShape n)
    (V : Fin n → ℝ) (t : Fin B.length → ℝ)
    (hV : ∀ i, ∑ a : Fin (B.size i), V (B.index i a) = 0) :
    ∑ a, V a * t (blockIndex B a) = 0 := by
  rw [← B.indexEquiv.sum_comp, Fintype.sum_sigma]
  change (∑ i, ∑ a : Fin (B.size i),
    V (B.index i a) * t (blockIndex B (B.index i a))) = 0
  simp_rw [blockIndex_index, ← Finset.sum_mul, hV]
  simp

/-- The supported fine parameter is orthogonal to every coarse real parameter,
with the target's literal transport and coordinate conventions. -/
theorem orthogonality_of_positiveRootParameter {n : ℕ}
    (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (v : Fin ((B.flatten Q).flatten R).length → ℝ)
    (hv : IsPositiveRootParameter (B.flatten Q) R v)
    (t : Fin B.length → ℝ) :
    ∑ a, (h ▸ v) (blockIndex (B.flatten S) a) * t (blockIndex B a) = 0 :=
  block_pairing_zero B _ t
    (positiveRootBlockSums.2.2 n B Q R S h v hv)

/-- Strictly decreasing coarse parameters repeat to an antitone diagonal vector. -/
theorem antitone_coarseParameter {n : ℕ} (B : BlockShape n)
    (t : Fin B.length → ℝ) (ht : StrictAnti t) :
    Antitone (fun a => t (blockIndex B a)) :=
  fun _ _ hab => ht.antitone (blockIndex_monotone B hab)

end Langlands.SupportedRegularWeylComparison
