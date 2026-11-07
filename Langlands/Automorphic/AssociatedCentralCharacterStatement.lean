import Langlands.Automorphic.AssociatedDeterminantTwistStatement

/-! # The central character of a weakly associated cuspidal realization

Henniart (1986), §4.3, uses that at the places of bad reduction the determinant of the
arithmetic representation matches the central character of the automorphic one; globally
this is Henniart (2000), §2.2: `det S = ω_Π ∘ τ_F`. Here the central character and the Hecke
character of `det S` are conclusions, not hypotheses: weak association of a representation
`S` of the relative Weil group of an arithmetic class family with the class of an actual
cuspidal realization `T` gives a Hecke character `ω` that is the central character of `T`
and satisfies `det S = ω ∘ τ_F`, and `ω` is the only Hecke character with either property.
Proposition definition only.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global

universe u uV uP

namespace RelativeWeilGroup

/-- Henniart (2000), §2.2, `det S = ω_Π ∘ τ_F`, with the central character concluded:
at an arithmetic class family, if `S` is weakly associated with the cuspidal class of the
actual cuspidal realization `T`, then some Hecke character `ω` is the central character of
`T` and satisfies `det S = ω ∘ τ_F`; every central character of `T` equals `ω`, and every
Hecke character `χ` with `det S = χ ∘ τ_F` equals `ω`. -/
def AssociatedCentralCharacterStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r),
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
    ∃ ω : HeckeCharacter F,
      T.HasCentralCharacter ω ∧
        FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω ∧
        (∀ ω' : HeckeCharacter F, T.HasCentralCharacter ω' → ω' = ω) ∧
        ∀ χ : HeckeCharacter F,
          FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E χ → χ = ω

end RelativeWeilGroup

end Langlands.ClassField.Global
