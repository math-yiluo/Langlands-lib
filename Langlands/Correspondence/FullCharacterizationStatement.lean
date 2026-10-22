import Langlands.Correspondence.FullFactorCompatibility
import Langlands.Correspondence.AssemblyLFactorStatement

/-!
# Characterization of the full correspondence by pair factors at one character

Two statements after Henniart 2002, for a full map `τ` that is compatible with rank
one for the geometrically normalized reciprocity candidate and with all pair L- and
epsilon-factors at one nontrivial additive character: `τ` extends the
supercuspidal correspondence (Corollary 1.6), and `τ` is its assembly
(Corollary 1.8). These are statements, not proofs.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Extension from factors at one character (statement only). Let `c0` be a
supercuspidal correspondence, `ψ` a nontrivial additive character and `e` the
geometrically normalized reciprocity candidate. If a full map `τ` is compatible with
rank one for `e` and, at `ψ`, with all pair L-factors and with all pair
epsilon-factors for some system with base component `e`, then `τ` sends the
zero-monodromy class of every irreducible Weil class `σ` to the supercuspidal class
`c0 σ`. -/
def FullCharacterizationExtendsStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (τ : FullMap.{uF, uP, uA} F)
    (ψ : NontrivialAdditiveCharacter F) (e : ReciprocityCandidate F),
    IsSupercuspidalCorrespondence F c0 → IsGeometricReciprocity F e →
      RankOneCompatibility F e τ → FullFactorCompatibilityAt F e ψ τ →
        ExtendsSupercuspidal F c0 τ

/-- Characterization from factors at one character (statement only). Under the
hypotheses of `FullCharacterizationExtendsStatement`, `τ` is the assembly of `c0`,
and every assembly of `c0` equals `τ`. -/
def FullCharacterizationStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (τ : FullMap.{uF, uP, uA} F)
    (ψ : NontrivialAdditiveCharacter F) (e : ReciprocityCandidate F),
    IsSupercuspidalCorrespondence F c0 → IsGeometricReciprocity F e →
      RankOneCompatibility F e τ → FullFactorCompatibilityAt F e ψ τ →
        IsAssemblyOf F c0 τ ∧ ∀ c : FullMap.{uF, uP, uA} F, IsAssemblyOf F c0 c → c = τ

end Langlands.Correspondence
