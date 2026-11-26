import Langlands.LocalField.Normalization.Proof

/-! # Equality of supplied and canonical p-adic local-field data -/

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

private theorem vle_iff_div_mem_integers (T : F.TopologicalData)
    (x y : F.Carrier) (hy : y ≠ 0) :
    @ValuativeRel.vle _ _ T.valuativeRel x y ↔ x / y ∈ T.Integers := by
  let := T.valuativeRel
  have hpos : 0 < ValuativeRel.valuation F.Carrier y :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hy)
  rw [(ValuativeRel.valuation F.Carrier).vle_iff_le, Valuation.mem_integer_iff,
    map_div₀, div_le_one₀ hpos]

private theorem vle_zero_iff_eq_zero (T : F.TopologicalData) (x : F.Carrier) :
    @ValuativeRel.vle _ _ T.valuativeRel x 0 ↔ x = 0 := by
  let := T.valuativeRel
  rw [(ValuativeRel.valuation F.Carrier).vle_iff_le, map_zero]
  simp

/-- Two supplied p-adic realizations on the same algebraic field have the same
module topology and the same valuative relation, hence equal data. -/
theorem eq_of_same_padicField (T U : F.TopologicalData) : T = U := by
  have ht := T.topology_eq_canonicalModule.trans U.topology_eq_canonicalModule.symm
  have hv : T.valuativeRel = U.valuativeRel := by
    apply ValuativeRel.ext
    funext x y
    apply propext
    by_cases hy : y = 0
    · subst y
      exact (vle_zero_iff_eq_zero T x).trans (vle_zero_iff_eq_zero U x).symm
    · exact (vle_iff_div_mem_integers T x y hy).trans
        ((T.canonicalNorm_le_one_iff_mem_integers (x / y)).symm.trans
          ((U.canonicalNorm_le_one_iff_mem_integers (x / y)).trans
            (vle_iff_div_mem_integers U x y hy).symm))
  cases T
  cases U
  cases ht
  cases hv
  rfl

end Langlands.PadicField.TopologicalData
