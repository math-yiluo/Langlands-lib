import Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Group.GL.SingleBlock

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- Cuspidality along the actual one-block embedding is GL supercuspidality. -/
theorem singleBlockCuspidalityClause {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) (n : ℕ) :
    SingleBlockCuspidalityClause.{uF, uV} T n := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro B hB V _ _ ρ
  rw [isSupercuspidal_iff_standard]
  change (IsAdmissible (ρ.comp (B.leviEmbedding F.Carrier)) ∧
    IsLeviQuasicuspidal B (ρ.comp (B.leviEmbedding F.Carrier))) ↔ _
  apply and_congr
  · simpa only [BlockShape.singleBlockLeviEquivContinuous_toMonoidHom] using
      isAdmissible_comp_continuousMulEquiv_iff ρ
        (B.singleBlockLeviEquivContinuous hB F.Carrier)
  · have hvan (S : BlockRefinement B) :
        Subsingleton (Jacquet.Coinvariants (ρ.comp (B.leviEmbedding F.Carrier))
          (refinedUnipotent F.Carrier B S)) ↔
        Subsingleton (Jacquet.Coinvariants ρ
          ((B.singleBlockRefinementEquiv hB S).unipotentSubgroup F.Carrier)) := by
      have h := (Jacquet.coinvariantsMapEquiv ρ (B.leviEmbedding F.Carrier)
        (refinedUnipotent F.Carrier B S)).toEquiv.subsingleton_congr
      rwa [B.singleBlock_refinedUnipotent_map hB F.Carrier S] at h
    constructor
    · intro h C hC
      obtain ⟨S, rfl⟩ := (B.singleBlockRefinementEquiv hB).surjective C
      exact (hvan S).mp (h S
        ((B.singleBlock_refinedParabolic_ne_top_iff hB F.Carrier S).mpr hC))
    · intro h S hS
      exact (hvan S).mpr (h (B.singleBlockRefinementEquiv hB S)
        ((B.singleBlock_refinedParabolic_ne_top_iff hB F.Carrier S).mp hS))

/-- Both exact cuspidality comparisons for every positive-rank p-adic GL. -/
theorem padicCuspidalityComparisonTheorems :
    PadicCuspidalityComparisonTheorems.{uF, uV} := by
  intro p _ F T n _
  exact ⟨standardJacquetSupercuspidalityClause T n, singleBlockCuspidalityClause T n⟩

example : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
      StandardJacquetSupercuspidalityClause.{uF, uV} T n ∧
      SingleBlockCuspidalityClause.{uF, uV} T n :=
  @padicCuspidalityComparisonTheorems

end Langlands.CuspidalSupport
