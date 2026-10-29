import Langlands.Representation.Classification.ProductLeviSquareIntegrableExponentNecessityStatement
import Langlands.Representation.Exponents.RefinedUpperSquareIntegrableCone

/-!
# Necessary whole-chamber bounds for square-integrable product Levis

The published strict blockwise cone theorem gives nonpositive pairing in every
original block, and negative pairing in any block with nonconstant absolute
values. Summing the pairings gives the norm bounds on the entire chamber.
-/

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear Geometric ProductLeviNecessity

universe uF uV

/-- Square integrability for one supplied Haar measure forces the weak bound
everywhere in the blockwise upper chamber and the strict bound whenever at least
one original block has nonconstant absolute values. -/
theorem glProductLeviSquareIntegrableExponentNecessity :
    GLProductLeviSquareIntegrableExponentNecessityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ B
  let := T.leviTopologicalGroup B
  intro M Q _ _ μ _ V _ _ σ hsq D ψ hψ hgen a ha
  obtain ⟨x, hx⟩ := T.exists_isRealPartOf ψ hψ
  have hcone := Exponents.RefinedUpperSquareIntegrableCone.isPositiveRootCone
    T B μ σ hsq D ψ hgen x hx
  have hmono : ∀ j : Fin B.length, Monotone (fun i : Fin (D j).length =>
      T.logAbs (a (B.flattenBlockEquiv D ⟨j, i⟩))) :=
    fun j i k hik => (T.logAbs_le_logAbs_iff _ _).mpr (ha j hik)
  have hnonpos : ∀ j : Fin B.length,
      ∑ i : Fin (D j).length, x (B.flattenBlockEquiv D ⟨j, i⟩) *
        (T.logAbs (a (B.flattenBlockEquiv D ⟨j, i⟩)) : ℝ) ≤ 0 := by
    intro j
    exact (Exponents.isClosedPositiveRootCone_iff_pairing _).mp
      (hcone j).isClosedPositiveRootCone |>.2 _ (hmono j)
  have hnorm := (PadicField.TopologicalData.isRealPartOf_iff_pairing T ψ x).mp hx a
  rw [sum_centreHMap_blocks T B D] at hnorm
  have hq := T.one_lt_residueCardinality_real
  constructor
  · rw [hnorm]
    calc
      _ ≤ (T.residueCardinality : ℝ) ^ (0 : ℝ) :=
        (Real.rpow_le_rpow_left_iff hq).mpr (Finset.sum_nonpos fun j _ => hnonpos j)
      _ = 1 := Real.rpow_zero _
  · rintro ⟨j, i, k, hik⟩
    have hne : ∃ i k : Fin (D j).length,
        T.logAbs (a (B.flattenBlockEquiv D ⟨j, i⟩)) ≠
          T.logAbs (a (B.flattenBlockEquiv D ⟨j, k⟩)) :=
      ⟨i, k, fun h => hik ((T.logAbs_eq_logAbs_iff _ _).mp h)⟩
    have hneg := (Exponents.isPositiveRootCone_iff_pairing _).mp (hcone j) |>.2 _ (hmono j) hne
    have hsum : (∑ j : Fin B.length, ∑ i : Fin (D j).length,
        x (B.flattenBlockEquiv D ⟨j, i⟩) *
          (T.logAbs (a (B.flattenBlockEquiv D ⟨j, i⟩)) : ℝ)) < 0 := by
      simpa using Finset.sum_lt_sum (fun j _ => hnonpos j) ⟨j, Finset.mem_univ j, hneg⟩
    rw [hnorm]
    calc
      _ < (T.residueCardinality : ℝ) ^ (0 : ℝ) :=
        (Real.rpow_lt_rpow_left_iff hq).mpr hsum
      _ = 1 := Real.rpow_zero _

end Langlands
