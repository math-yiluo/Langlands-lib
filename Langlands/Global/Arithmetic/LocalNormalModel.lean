import Langlands.LocalField.Definitions
import Langlands.Global.Arithmetic.RationalGaloisModel

/-! # A totally real rational model of a local normal closure -/

noncomputable section

namespace Langlands.Global.FieldRealization

universe u

/-- The normal closure of a supplied finite p-adic field inside its algebraic closure. -/
abbrev localNormalClosure (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) :=
  IntermediateField.normalClosure (Padic p) E.Carrier (AlgebraicClosure E.Carrier)

instance localNormalClosure_charZero (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) :
    CharZero (localNormalClosure p E) :=
  charZero_of_injective_algebraMap
    (algebraMap (Padic p) (localNormalClosure p E)).injective

instance localNormalClosure_isGalois (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) :
    IsGalois (Padic p) (localNormalClosure p E) := ⟨⟩

/-- A Type-0 totally real rational Galois model of the local normal closure. -/
abbrev localNormalModel (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) : Type :=
  rationalGaloisModel p (localNormalClosure p E)

/-- The rational model embeds in the normal closure of the original local field. -/
def localNormalModelEmbedding (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) :
    localNormalModel p E →+* localNormalClosure p E :=
  (rationalGaloisModelEmbedding p (localNormalClosure p E)).toRingHom

theorem localNormalModelEmbedding_adjoin (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) :
    IntermediateField.adjoin (Padic p) (Set.range (localNormalModelEmbedding p E)) = ⊤ :=
  rationalGaloisModelEmbedding_adjoin p (localNormalClosure p E)

end Langlands.Global.FieldRealization
