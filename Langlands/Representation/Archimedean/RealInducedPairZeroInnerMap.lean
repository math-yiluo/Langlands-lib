import Langlands.Representation.Archimedean.RealInducedPairOuterReorder
import Langlands.Representation.Archimedean.RealInducedPairLinkedIncoming
import Langlands.Representation.Archimedean.RealCharacterInducedWeightZero

/-! # An actual replacement target at zero signed inner weight -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealInducedPairZeroInnerMap

open RealStandardFiltration RealInducedPairLinkedReplacement
open RealInducedPairFrobenius RealInducedPairOuterReorder InductionStages

variable {d e : ComplexCharacterData} {k : ℕ}
  (h : IsLinkedAt d e k)
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
  (hH : innerWeight d e k = 0)

include hH in
/-- At the zero inner weight both original absolute weights are positive. -/
theorem weights_pos : 0 < d.weight.natAbs ∧ 0 < e.weight.natAbs := by
  have hmin : (min d.weight.natAbs e.weight.natAbs : ℤ) = (k : ℤ) + 1 := by
    dsimp [innerWeight] at hH
    omega
  have hd := min_le_left d.weight.natAbs e.weight.natAbs
  have he := min_le_right d.weight.natAbs e.weight.natAbs
  omega

include hH in
@[simp] theorem inner_weight : (innerData d e k).weight = 0 := by
  simpa only [innerData, characterOfParams_weight] using hH

include h hp hH in
/-- The first remaining character is the sign character of the zero-weight block. -/
theorem first_eq : first d = RealJacquetFrobenius.charData 1 (innerData d e k).exponent := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hpar : (d.weight.natAbs + 1) % 2 = 1 := by
    rw [Int.even_iff] at hp
    omega
  have hc : (⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = 1 := by
    apply Fin.ext
    exact hpar
  change RealJacquetFrobenius.charData _ _ = RealJacquetFrobenius.charData 1 _
  rw [hc]
  congr 1
  have heq := (endpoint_equalities h).2.2.2
  rw [hH, Int.cast_zero, zero_div, sub_zero] at heq
  exact heq.symm

include h hH in
/-- The second remaining character is the even character of the zero-weight block. -/
theorem second_eq : second e = RealJacquetFrobenius.charData 0 (innerData d e k).exponent := by
  change RealJacquetFrobenius.charData 0 _ = RealJacquetFrobenius.charData 0 _
  congr 1
  have heq := (endpoint_equalities h).2.2.1
  rw [hH, Int.cast_zero, zero_div, add_zero] at heq
  exact heq.symm

include h hp hH in
/-- Expanding only the zero inner block identifies the reordered outer target. -/
theorem kf_reordered : KF 4 (reorderedList d e k) = KF 4 (replacementPair d e k) := by
  have hexp : realBlockExpand (.induced (innerData d e k)) =
      [.character (first d), .character (second e)] := by
    rw [first_eq h hp hH, second_eq h hH]
    simp only [realBlockExpand, inner_weight hH, ite_eq_left]
  have heq := kf_append_expand 4 [.induced (outerData d e k)] []
    (.induced (innerData d e k))
  simpa only [hexp, List.cons_append, List.nil_append, List.append_nil,
    reorderedList, replacementPair] using heq.symm

/-- An exact standard intertwiner is an intertwiner modulo the zero subspace. -/
theorem modulo_of_standard {n : ℕ} {ds es : List RealBlock}
    {T : KFin n ds →ₗ[ℂ] KFin n es}
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T) :
    IsRealIntertwinerModulo n ds es ⊥ T := by
  obtain ⟨hk, hl⟩ := isRealStandardIntertwiner_iff.mp hT
  apply isRealIntertwinerModulo_iff.mpr
  exact ⟨fun k f => by rw [hk, sub_self]; exact Submodule.zero_mem _,
    fun X f => by rw [hl, sub_self]; exact Submodule.zero_mem _⟩

/-- The mixed outer target is the actual replacement pair at the zero boundary. -/
def replacementEquiv : KF 4 (mixedList d e k) ≃ₗ[ℂ] KF 4 (replacementPair d e k) :=
  (reorderEquiv h (weights_pos hH).1).trans (LinearEquiv.ofEq _ _ (kf_reordered h hp hH))

include h hp hH

theorem replacementEquiv_exact :
    IsRealIntertwinerModulo 4 (mixedList d e k) (replacementPair d e k) ⊥
      (replacementEquiv h hp hH).toLinearMap :=
  modulo_comp_bot (modulo_ofEqMap (kf_reordered h hp hH))
    (modulo_of_standard (reorderEquiv_intertwiner h (weights_pos hH).1))

/-- The outer tail with the actual two-block replacement as its codomain. -/
def replacementMap : KF 4 (src d e) →ₗ[ℂ] KF 4 (replacementPair d e k) :=
  (replacementEquiv h hp hH).toLinearMap.comp (RealInducedPairOuterTail.outerMap h hp)

theorem replacementMap_exact :
    IsRealIntertwinerModulo 4 (src d e) (replacementPair d e k) ⊥
      (replacementMap h hp hH) :=
  modulo_comp_bot (replacementEquiv_exact h hp hH) (RealInducedPairOuterTail.outerMap_exact h hp)

theorem ker_replacementMap :
    LinearMap.ker (replacementMap h hp hH) =
      LinearMap.ker (RealInducedPairOuterTail.outerMap h hp) :=
  LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective (replacementEquiv h hp hH).injective)

/-- The actual incoming image is killed by the replacement-target map. -/
theorem replacementMap_comp_swap {μ₁ μ₀ μ₂ : ℤ → ℂ}
    (hm : MultiplierData e d (swapParameter e d) μ₁ μ₀ μ₂
      (RealInducedPairLinkedIncoming.lastMultiplier d e k)) :
    (replacementMap h hp hH).comp hm.swap = 0 := by
  apply LinearMap.ext
  intro f
  change replacementEquiv h hp hH (RealInducedPairOuterTail.outerMap h hp (hm.swap f)) = 0
  rw [RealInducedPairLinkedIncoming.outerMap_swap_eq_zero h hp hm, map_zero]

end RealInducedPairZeroInnerMap

open RealStandardFiltration RealInducedPairFrobenius
  RealInducedPairLinkedReplacement RealInducedPairZeroInnerMap in
/-- At zero signed inner weight, the actual outer tail has an exact replacement target. -/
def RealInducedPairZeroInnerMapStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    innerWeight d e k = 0 →
      ∃ T : KF 4 (src d e) →ₗ[ℂ] KF 4 (replacementPair d e k),
        IsRealIntertwinerModulo 4 (src d e) (replacementPair d e k) ⊥ T ∧
          LinearMap.ker T = LinearMap.ker (RealInducedPairOuterTail.outerMap h hp)

open RealInducedPairZeroInnerMap in
theorem realInducedPairZeroInnerMap : RealInducedPairZeroInnerMapStatement := by
  intro d e k h hp hH
  exact ⟨replacementMap h hp hH, replacementMap_exact h hp hH, ker_replacementMap h hp hH⟩

end Langlands.Archimedean
