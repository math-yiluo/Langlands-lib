import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.Unramified.RelativeWeilAssociation
import Langlands.Weil.Representation.Dual

/-! # Contragredients of weakly associated pairs

Henniart (2000), §2.2: if a representation `S` of the Weil group and an automorphic
representation `Π` are associated, then so are the contragredients `S^∨` and `Π^∨`. Stated
for representations of the class-indexed extension `RelativeWeilGroup c F E` of every class
family `c`, and for actual cuspidal realizations and classes. That extension is the relative
Weil group `W_{E/F}` only when `c F E` is the arithmetic fundamental class; the statement for
other families is a derived generalization. Proposition definitions only.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global Langlands.Unramified

universe u uV uP uQ

namespace RelativeWeilGroup

/-- Presented form of Henniart (2000), §2.2, for the contragredient: if `S` is weakly
associated with the spectral system of a presentation `P` of an actual cuspidal realization
`T`, and `T'` realizes the contragredient of `T`, then the algebraic dual of `S` is weakly
associated with the spectral system of every presentation `P'` of `T'`. -/
def PresentedContragredientAssociationStatement : Prop :=
  ∀ (c : FundamentalClass.ClassFamily.{u}) (F E : Type u) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uP} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'),
    T'.realization.IsContragredientOf T.realization →
    IsWeaklyAssociated S P.spectralSystem →
    IsWeaklyAssociated (FiniteRepresentation.dual S) P'.spectralSystem

/-- Henniart (2000), §2.2, for the contragredient, for cuspidal classes: if `S` is weakly
associated with the actual cuspidal class `π` and `π'` is a contragredient of `π`, then the
algebraic dual of `S` is weakly associated with `π'`. -/
def ClassContragredientAssociationStatement : Prop :=
  ∀ (c : FundamentalClass.ClassFamily.{u}) (F E : Type u) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (π π' : Automorphic.CuspidalOperatorRealization.IsoClass F r),
    π'.IsContragredientOf π →
    IsWeaklyAssociatedClass.{u, uV, uP} S π →
    IsWeaklyAssociatedClass.{u, uV, uQ} (FiniteRepresentation.dual S) π'

/-- The contragredient assertion of Henniart (2000), §2.2, at the level of the class-indexed
extensions, in presented and class form. -/
def AssociatedContragredientStatement : Prop :=
  PresentedContragredientAssociationStatement.{u, uV, uP, uQ} ∧
    ClassContragredientAssociationStatement.{u, uV, uP, uQ}

end RelativeWeilGroup

end Langlands.ClassField.Global
