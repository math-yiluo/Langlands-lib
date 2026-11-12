import Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonStatement

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The comparison with positive carry symbols using geometric inverse cup.
This is an alternative explicit comparison premise, with no assertion that it
or the arithmetic comparison has been proved. -/
def FiniteGeometricCupArtinCharacterComparison : Prop :=
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
            (geometricReciprocityOfCup F.Carrier D c h
              (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) =
          Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a)

end Langlands.ClassFieldTheory.Local
