import Langlands.Correspondence.FullCharacterizationExtendsProof
import Langlands.Correspondence.AssemblyLCharacterizationProof

/-!
# Henniart's characterization of the full correspondence at one character

Henniart 2002, Corollary 1.8 (proof in Section 4.5): the published extension
theorem `fullCharacterizationExtends` (Corollary 1.6) gives that `τ` extends the
supercuspidal correspondence, and the published L-factor characterization of
the assembly `assemblyLCharacterization` (Theorem 1.8) then identifies `τ` with
the assembly.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Henniart 2002, Corollary 1.8: a full map compatible with rank one and with all
pair L- and epsilon-factors at one nontrivial additive character is the assembly
of the supercuspidal correspondence, and every assembly of it equals that map. -/
theorem fullCharacterization : FullCharacterizationStatement.{uF, uP, uA} F := by
  intro c0 τ ψ e hc0 he hRankOne hFactors
  apply assemblyLCharacterization F c0 τ ψ hc0
    (fullCharacterizationExtends F c0 τ ψ e hc0 he hRankOne hFactors)
  intro k j _ D D' _ _
  exact hFactors.1 k j D D'

end Langlands.Correspondence
