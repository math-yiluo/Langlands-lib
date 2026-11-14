import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ZeroRankEmbeddingProof
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem MinimalNonzeroJacquetTheorem NonassociatedJacquetSubquotientsTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem cuspidalEmbedding minimalNonzeroJacquet normalizedQuasicuspidalEmbedding normalizedQuasicuspidalEmbedding_of zeroRankCuspidalEmbedding
open Langlands.GeneralLinear
universe uF uV

variable (F : LocalFieldPackage.{uF})
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

end Langlands.AllFieldBZ.CuspidalSupport
