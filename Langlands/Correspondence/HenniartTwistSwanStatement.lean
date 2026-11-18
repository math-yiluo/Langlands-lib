import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.HarmonicAnalysis.Conductor

/-!
# Swan exponents of character twists of supercuspidal classes

The character Swan exponent, the determinant twist, and the supercuspidal
consequence of Lemma `lem:level`(ii) in the operator's numerical LLC route note.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uV

open Langlands.Correspondence

namespace Numerical

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The rank-one Swan exponent, obtained by truncated subtraction of one
from the multiplicative conductor. -/
def characterSwanExponent (χ : QuasiCharacter K) : ℕ :=
  K.canonicalTopologicalData.multiplicativeConductor χ - 1

/-- Twist a rank-`k + 1` supercuspidal class by `χ ∘ det`. -/
def supercuspidalCharacterTwist (k : ℕ) (χ : QuasiCharacter K) :
    SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat ≃
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat :=
  supercuspidalTwistEquiv K k.succPNat χ

end Numerical

open Numerical

/-- The supercuspidal Swan bound of the route note's Lemma `lem:level`(ii),
with equality when the two exponents in the maximum differ. -/
def SupercuspidalTwistSwanBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (χ : QuasiCharacter K) (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) (s : ℕ),
    HasSupercuspidalSwan K π s →
      ∃ s' : ℕ, HasSupercuspidalSwan K (supercuspidalCharacterTwist K k χ π) s' ∧
        s' ≤ max s ((k + 1) * characterSwanExponent K χ) ∧
        (s ≠ (k + 1) * characterSwanExponent K χ →
          s' = max s ((k + 1) * characterSwanExponent K χ))

end Langlands.Henniart
