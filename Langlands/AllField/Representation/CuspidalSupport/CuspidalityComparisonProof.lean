import Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalityComparisonStatement
namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding SingleBlockCuspidalityClause singleBlockCuspidalityClause
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

/-- Cuspidality along the actual one-block embedding is GL supercuspidality. -/
theorem singleBlockCuspidalityClause 
    {F : Type uF} [Field F] (T : LocalFieldData F) (n : ℕ) :
    SingleBlockCuspidalityClause.{uF, uV} T n := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro B hB V _ _ ρ
  rw [isSupercuspidal_iff_standard]
  change (IsAdmissible (ρ.comp (B.leviEmbedding F)) ∧
    IsLeviQuasicuspidal B (ρ.comp (B.leviEmbedding F))) ↔ _
  apply and_congr
  · simpa only [BlockShape.singleBlockLeviEquivContinuous_toMonoidHom] using
      isAdmissible_comp_continuousMulEquiv_iff ρ
        (B.singleBlockLeviEquivContinuous hB F)
  · have hvan (S : BlockRefinement B) :
        Subsingleton (Jacquet.Coinvariants (ρ.comp (B.leviEmbedding F))
          (refinedUnipotent F B S)) ↔
        Subsingleton (Jacquet.Coinvariants ρ
          ((B.singleBlockRefinementEquiv hB S).unipotentSubgroup F)) := by
      have h := (Jacquet.coinvariantsMapEquiv ρ (B.leviEmbedding F)
        (refinedUnipotent F B S)).toEquiv.subsingleton_congr
      rwa [B.singleBlock_refinedUnipotent_map hB F S] at h
    constructor
    · intro h C hC
      obtain ⟨S, rfl⟩ := (B.singleBlockRefinementEquiv hB).surjective C
      exact (hvan S).mp (h S
        ((B.singleBlock_refinedParabolic_ne_top_iff hB F S).mpr hC))
    · intro h S hS
      exact (hvan S).mpr (h (B.singleBlockRefinementEquiv hB S)
        ((B.singleBlock_refinedParabolic_ne_top_iff hB F S).mp hS))

end Langlands.AllField.CuspidalSupport
