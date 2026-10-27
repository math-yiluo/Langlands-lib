import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.FiniteOrderDeterminantTwist
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.Twist
import Langlands.ClassField.Global.RelativeWeilTransfer

/-! # Determinants and twists of weakly associated pairs

Henniart (2000), §2.2: if a representation `S` of the Weil group and a cuspidal automorphic
representation `Π` are associated, then `det S = ω_Π ∘ τ_F`, where `ω_Π` is the central
character of `Π`; and for a character `χ` of `C_F`, `(χ ∘ τ_F) ⊗ S` and `(χ ∘ det) ⊗ Π` are
associated. Stated for representations of the relative Weil group `W_{E/F}` of an arithmetic
fundamental class family. At finite level, `τ_F` is the pointwise inverse of the transfer
`W_{E/F} → C_F`. The twist is stated for finite-order characters only. Proposition
definitions only.
-/

noncomputable section

namespace Langlands.ClassField.Global

open scoped NumberField
open Langlands.Global

universe u uV uP uQ

namespace RelativeWeilGroup

/-- The character `χ ∘ τ_F` of `W_{E/F}`, where `τ_F` is the pointwise inverse of the
transfer `W_{E/F} → C_F`. -/
def reciprocityCharacter (c : FundamentalClass.ClassFamily.{u}) (F E : Type u) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) : RelativeWeilGroup c F E →* ℂˣ :=
  ((χ : NumberField.IdeleClassGroup (𝓞 F) F →* ℂˣ).comp (transfer c F E))⁻¹

@[simp]
theorem reciprocityCharacter_apply (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (w : RelativeWeilGroup c F E) :
    reciprocityCharacter c F E χ w = (χ (transfer c F E w))⁻¹ :=
  rfl

/-- Henniart (2000), §2.2, for the determinant, presented form: at an arithmetic class
family, if `S` is weakly associated with the spectral system of a presentation of an actual
cuspidal realization `T` with central character `ω`, then `det S = ω ∘ τ_F`. -/
def PresentedDeterminantAssociationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uP} T)
    (ω : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ),
    T.HasCentralCharacter ω →
    IsWeaklyAssociated S P.spectralSystem →
    FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω

/-- Henniart (2000), §2.2, for finite-order twists, presented form: at an arithmetic class
family, if `S` is weakly associated with the spectral system of a presentation of `T`, and
`T'` is the twist of `T` by `χ ∘ det` for a finite-order Hecke character `χ`, then
`(χ ∘ τ_F) ⊗ S` is weakly associated with the spectral system of every presentation of
`T'`. -/
def PresentedTwistAssociationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uP} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T') (χ : HeckeCharacter F),
    Automorphic.CuspidalOperatorRealization.IsFiniteOrderDeterminantTwist χ T T' →
    IsWeaklyAssociated S P.spectralSystem →
    IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
      P'.spectralSystem

/-- Henniart (2000), §2.2, for finite-order twists, for cuspidal classes. -/
def ClassTwistAssociationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (π π' : Automorphic.CuspidalOperatorRealization.IsoClass F r) (χ : HeckeCharacter F),
    π.IsFiniteOrderDeterminantTwist χ π' →
    IsWeaklyAssociatedClass.{u, uV, uP} S π →
    IsWeaklyAssociatedClass.{u, uV, uQ}
      (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) π'

/-- The determinant and finite-order twist assertions of Henniart (2000), §2.2. -/
def AssociatedDeterminantTwistStatement : Prop :=
  PresentedDeterminantAssociationStatement.{u, uV, uP} ∧
    PresentedTwistAssociationStatement.{u, uV, uP, uQ} ∧
    ClassTwistAssociationStatement.{u, uV, uP, uQ}

end RelativeWeilGroup

end Langlands.ClassField.Global
