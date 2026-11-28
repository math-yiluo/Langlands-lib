import Langlands.Representation.CuspidalSupport.SupercuspidalRemarksReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.2.1, remarks: proof

The three remarks of `SupercuspidalRemarksStatements` (subquotients of supercuspidal
representations are supercuspidal; with compact centre, supercuspidal is equivalent to
compact; supercuspidality is equivalent to the functions `f_{K,w}` having support compact
modulo the centre), obtained by applying `supercuspidalRemarksReduction` to the proof
`jointSpecialCompactBasisExistence` of its premise. -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.2.1, remarks: every subquotient of a supercuspidal representation is
supercuspidal; if the centre `Z` of `G(F)` is compact, supercuspidal is equivalent to
having compactly supported coefficients; and `A` is supercuspidal if and only if, for every
compact open `K` and every `w ∈ A`, the functions `g ↦ ℓ(A(g⁻¹) w)` with `ℓ` a
`K`-invariant linear form have support in one set `C Z` with `C` compact. -/
theorem supercuspidalRemarks : SupercuspidalRemarksStatements.{u, v} :=
  supercuspidalRemarksReduction
    Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.Aubert.General.RepresentedParabolic
