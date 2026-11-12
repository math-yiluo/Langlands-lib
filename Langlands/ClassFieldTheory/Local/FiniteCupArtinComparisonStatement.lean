import Langlands.ClassFieldTheory.Local.TateAbelianization
import Langlands.ClassFieldTheory.Local.FiniteArtinSymbol

/-!
# Character comparison of finite inverse-cup reciprocity and Artin symbols
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Arithmetic inverse-cup reciprocity for the canonical positive fundamental
class has the character values of the published finite Artin construction.
The finite Galois group is not required to be abelian. -/
def FiniteCupArtinCharacterComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]
    (c : relativeCohomology F.Carrier D 2),
    IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c →
    ∀ (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c)),
      letI : NeZero (Module.finrank F.Carrier D) := ⟨Module.finrank_pos.ne'⟩
      ∀ (ψ : Gal(D/F.Carrier) →*
          Multiplicative (ZMod (Module.finrank F.Carrier D)))
        (a : F.Carrierˣ),
        Abelianization.lift ψ
            (arithmeticReciprocityOfCup F.Carrier D c h
              (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) =
          Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a)

end Langlands.ClassFieldTheory.Local
