import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.ConjugateContragredient

/-!
# Arithmetic transport of three properties of cuspidal classes

Statements only. For a ring isomorphism `e : K ≃+* L` of number fields, the
arithmetic pullback `arithmeticComap e` moves cuspidal realizations and classes
over `L` to `K`. The three statements assert that it preserves a unitary central
character, a supercuspidal component (at the place `finitePlaceEquiv e w` of `K`
corresponding to the place `w` of `L`), and, between CM fields, conjugate
self-duality. Galois conjugation `galoisConj σ = arithmeticComap σ.symm` is the
special case `K = L`. No existence or transport theorem is proved here.
-/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.Automorphic

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality

/-- Arithmetic pullback along a ring isomorphism `e : K ≃+* L` preserves a
unitary central character: if the cuspidal realization `S` over `L` has a
unitary central character, so has `S.arithmeticComap e` over `K`. -/
def ArithmeticComapUnitaryCentralCharacterStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) (r : ℕ) (S : CuspidalOperatorRealization L r),
    ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter (S.arithmeticComap e)

/-- Arithmetic pullback along a ring isomorphism `e : K ≃+* L` preserves a
supercuspidal component: if the cuspidal class `c` over `L` has a supercuspidal
component at the finite place `w` of `L`, then its pullback over `K` has a
supercuspidal component at the corresponding place `finitePlaceEquiv e w`. -/
def ArithmeticComapSupercuspidalComponentStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) (r : ℕ) (c : CuspidalOperatorRealization.IsoClass L r)
    (w : Langlands.Global.FinitePlace L),
    c.HasSupercuspidalComponent.{uL, uV} w →
      (CuspidalOperatorRealization.IsoClass.arithmeticComap e c).HasSupercuspidalComponent.{uK, uV}
        (finitePlaceEquiv e w)

/-- Arithmetic pullback along a ring isomorphism `e : K ≃+* L` of CM fields
preserves conjugate self-duality of cuspidal classes. -/
def ArithmeticComapConjugateSelfDualStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [IsCMField K]
    [Field L] [NumberField L] [IsCMField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) (r : ℕ) (c : CuspidalOperatorRealization.IsoClass L r),
    c.IsConjugateSelfDual →
      (CuspidalOperatorRealization.IsoClass.arithmeticComap e c).IsConjugateSelfDual

end Langlands.Automorphic
