import Langlands.Representation.CuspidalSupport.LeviCompactPart
import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly

/-! Quasicuspidal decomposition of arbitrary smooth product-Levi representations. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- The exact quasicuspidal decomposition proposition, including the empty-product
boundary case, with no additional representation hypotheses. -/
theorem leviQuasicuspidalDecomposition {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviQuasicuspidalDecompositionTheorem.{uF, uV} F T B := by
  cases n with
  | zero =>
    let := T.topology
    have hsize (i : Fin B.length) : B.size i ≤ 0 := by
      calc
        B.size i ≤ ∑ j, B.size j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = 0 := B.sum_eq
    let : IsEmpty (Fin B.length) :=
      ⟨fun i => (Nat.not_lt_of_ge (hsize i)) (B.positive i)⟩
    have hqc (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
        IsLeviQuasicuspidal B A.representation := by
      intro S hS
      exact (hS (Subsingleton.elim _ _)).elim
    exact SmoothRep.decomposition_of_natural_idempotent
      (fun A => IsLeviQuasicuspidal B A.representation)
      (fun A => Representation.IntertwiningMap.id A.representation)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl)
      (fun A => hqc _) (fun _ _ _ => rfl)
  | succ n =>
    exact leviQuasicuspidalDecomposition_of_inputs T B
      (determinantUnitIsotypic_isCompl T B)
      (compactCoefficientFixedLevelFiniteness p F T (n + 1) (Nat.succ_pos n) B)
      (determinantUnitTotalIsotypic_compact T B)
      (determinantUnitTotalIsotypic_exhaust T B)
      leviHarishChandraTheorem

end Langlands.CuspidalSupport
