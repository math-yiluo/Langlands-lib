import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.AllField.Representation.CuspidalSupport.ZeroRankEmbeddingProof
import Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof
namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem MinimalNonzeroJacquetTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem cuspidalEmbedding minimalNonzeroJacquet normalizedQuasicuspidalEmbedding normalizedQuasicuspidalEmbedding_of zeroRankCuspidalEmbedding
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F)

/-- Every irreducible smooth representation of an actual GL_n is admissible
and embeds into normalized induction from an irreducible cuspidal standard Levi
representation, including rank zero and independent carrier universes. -/
theorem cuspidalEmbedding (n : ℕ) :
    CuspidalEmbeddingTheorem.{uF, uV} F T n := by
  cases n with
  | zero => exact zeroRankCuspidalEmbedding F T
  | succ n =>
    let := T.topology
    let := T.generalLinearTopologicalGroup (n + 1)
    intro ω hω
    obtain ⟨B, σ, hσ, hqc, j, hj⟩ :=
      normalizedQuasicuspidalEmbedding F T (n + 1) (Nat.zero_lt_succ n) ω hω
    have hσadm : σ.IsAdmissible :=
      Langlands.AllField.CuspidalSupport.LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T B σ hσ hqc
    have hind :=
      Langlands.AllField.Parabolic.normalizedInductionAdmissibility F T B σ σ.representation hσadm
    exact ⟨isAdmissible_of_injective j hj hind,
      B, σ, hσ, ⟨hσadm, hqc⟩, j, hj⟩

end Langlands.AllField.CuspidalSupport
