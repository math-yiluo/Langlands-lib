import Langlands.Galois.AbsoluteTopologyProof
import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerUpperSupProof

/-! # Upper ramification transitivity on the infinite Kummer tower -/

namespace Langlands.Ramification.Kummer

open _root_.Langlands.Ramification.Padic

universe u

/-- The fixing subgroup of the infinite Kummer tower and the absolute
upper group generate the absolute Galois group through the first break. -/
theorem kummerTowerLimitUpperSup : KummerTowerLimitUpperSupStatement.{u} := by
  intro p hp F ϖ πs hπ v hv hmax
  let := GaloisRepresentation.absoluteGaloisGroupCompactness F.Carrier
  let stageFixing (n : ℕ) : Subgroup (Field.absoluteGaloisGroup F.Carrier) :=
    (kummerStage F πs n).field.fixingSubgroup
  let towerFixing : Subgroup (Field.absoluteGaloisGroup F.Carrier) :=
    (kummerTower F πs).fixingSubgroup
  let upper := absoluteUpperRamificationGroup F v
  have : upper.Normal := absoluteUpperRamificationGroup_normal F v
  have hstage (n : ℕ) : (kummerStage F πs n).field ≤ (kummerStage F πs (n + 1)).field := by
    change IntermediateField.adjoin F.Carrier {πs n} ≤
      IntermediateField.adjoin F.Carrier {πs (n + 1)}
    rw [IntermediateField.adjoin_simple_le_iff, ← hπ.2.2 n]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self F.Carrier (πs (n + 1))) p
  change towerFixing ⊔ upper = ⊤
  apply top_unique
  intro σ _
  let S (n : ℕ) : Set (Field.absoluteGaloisGroup F.Carrier) :=
    {τ | τ ∈ stageFixing n ∧ τ⁻¹ * σ ∈ upper}
  have hstep (n : ℕ) : S (n + 1) ⊆ S n :=
    fun _ h => ⟨IntermediateField.fixingSubgroup_le (hstage n) h.1, h.2⟩
  have hclosed (n : ℕ) : IsClosed (S n) :=
    (kummerStage F πs n).field.fixingSubgroup_isClosed.inter
      ((absoluteUpperRamificationGroup_isClosed F v).preimage
        (continuous_inv.mul continuous_const))
  have hnonempty (n : ℕ) : (S n).Nonempty := by
    have hsup : stageFixing n ⊔ upper = ⊤ := kummerTowerUpperSup p F ϖ πs hπ n v hv hmax
    have hσ : σ ∈ stageFixing n ⊔ upper := by
      rw [hsup]
      exact Subgroup.mem_top σ
    obtain ⟨τ, hτ, δ, hδ, hmul⟩ := Subgroup.mem_sup_of_normal_right.mp hσ
    refine ⟨τ, hτ, ?_⟩
    rwa [← hmul, inv_mul_cancel_left]
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnonempty (hclosed 0).isCompact hclosed
  have hfix : τ ∈ towerFixing := by
    have hle : kummerTower F πs ≤ IntermediateField.fixedField
        (Subgroup.zpowers (G := Gal(AlgebraicClosure F.Carrier/F.Carrier)) τ) :=
      iSup_le fun n => (IntermediateField.le_iff_le _ _).mpr
        (Subgroup.zpowers_le.mpr (Set.mem_iInter.mp hτ n).1)
    exact (Subgroup.zpowers_le (G := Gal(AlgebraicClosure F.Carrier/F.Carrier))).mp
      ((IntermediateField.le_iff_le _ _).mp hle)
  exact Subgroup.mem_sup_of_normal_right.mpr
    ⟨τ, hfix, τ⁻¹ * σ, (Set.mem_iInter.mp hτ 0).2, mul_inv_cancel_left _ _⟩

end Langlands.Ramification.Kummer
