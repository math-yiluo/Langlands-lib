import Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

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
      LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T B σ hσ hqc
    have hind :=
      Parabolic.normalizedInductionAdmissibility F T B σ σ.representation hσadm
    exact ⟨isAdmissible_of_injective j hj hind,
      B, σ, hσ, ⟨hσadm, hqc⟩, j, hj⟩

end Langlands.CuspidalSupport
