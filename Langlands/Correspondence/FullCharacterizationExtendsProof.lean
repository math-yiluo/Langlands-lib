import Langlands.Correspondence.FullCharacterizationExtendsReduction
import Langlands.Representation.RankinSelberg.SupercuspidalLocalConverseProof
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationProof
import Langlands.LocalFactor.NonabelianUniquenessProof

/-!
# Henniart's extension from full pair factors at one character

Henniart 2002, Corollary 1.6 (proof in Section 3.4): the published conditional
reduction `fullCharacterizationExtends_of_inputs` applied to the published
proofs of its three inputs, the supercuspidal local converse theorem,
Theorem 1.6(b), and uniqueness of local-constant systems.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Henniart 2002, Corollary 1.6: under the hypotheses of the full
characterization at one additive character, `τ` extends the supercuspidal
correspondence `c0`. -/
theorem fullCharacterizationExtends :
    FullCharacterizationExtendsStatement.{uF, uP, uA} F :=
  fullCharacterizationExtends_of_inputs F RankinSelberg.supercuspidalLocalConverse
    RankinSelberg.supercuspidalLFactorCharacterization
    (fun eC => LocalFactor.NonabelianSystem.unique F eC)

end Langlands.Correspondence
