import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.Automorphic.OperatorCMTransportClasses
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Global.HeckeCharacterTransport

/-! # Finite-character correction in Harris's Lemma 1.6 -/

noncomputable section

universe uE uD uV uW

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality Langlands.Automorphic Langlands.Automorphic.Unramified

/-- The arithmetic conjugate of the contragredient of a weak descent of a
conjugate self-dual class belongs to the same weak descent fibre. -/
def WeakBaseChangeConjugateDualDescentStatement : Prop :=
  ∀ (E : Type uE) (D : Type uD) [Field E] [NumberField E] [IsCMField E]
    [Field D] [NumberField D] [IsCMField D] [Algebra E D]
    [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient D)]
    (r : ℕ) (S Sdual : CuspidalOperatorRealization E r) (T : CuspidalOperatorRealization D r),
    Sdual.realization.IsContragredientOf S.realization →
    T.isoClass.IsConjugateSelfDual →
    CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW}
      T.isoClass S.isoClass →
    CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW}
      T.isoClass Sdual.complexConj.isoClass

/-- A character trivial on CM cyclic norms is the pullback of a finite
character of the maximal totally real subfield, trivial at infinity. -/
def CMNormKernelRealFactorStatement : Prop :=
  ∀ (E : Type uE) (D : Type uD) [Field E] [NumberField E] [IsCMField E]
    [Field D] [NumberField D] [IsCMField D] [Algebra E D] [IsGalois E D]
    [IsCyclic (D ≃ₐ[E] D)] (η : HeckeCharacter E),
    η.IsTrivialOnNorm D →
    ∃ η₀ : HeckeCharacter (maximalRealSubfield E),
      η₀.HasFiniteOrder ∧ η₀.atInfinity = 1 ∧
      η = η₀.comp (ideleClassNorm (K := maximalRealSubfield E) (L := E))

/-- A finite real-subfield character trivial at infinity extends to a finite
CM character. The product with its CM conjugate is the real norm pullback. -/
def CMFiniteRealCharacterExtensionStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E]
    (η₀ : HeckeCharacter (maximalRealSubfield E)),
    η₀.HasFiniteOrder → η₀.atInfinity = 1 →
    ∃ α : HeckeCharacter E,
      α.HasFiniteOrder ∧
      α.comp (ideleClassInclusion (K := maximalRealSubfield E) (L := E)) = η₀ ∧
      α * α.complexConj = η₀.comp (ideleClassNorm (K := maximalRealSubfield E) (L := E))

/-- Twisting an actual cuspidal realization by the correcting finite character
makes it conjugate self-dual while retaining the hypotheses for Theorem 1.2. -/
def FiniteCharacterConjugateDualCorrectionStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (S Sdual : CuspidalOperatorRealization E r) (v : FinitePlace E)
    (α : HeckeCharacter E) (hα : α.HasFiniteOrder),
    Sdual.realization.IsContragredientOf S.realization →
    S.isoClass.IsFiniteOrderDeterminantTwist (α * α.complexConj)
      Sdual.complexConj.isoClass →
    ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
    S.isoClass.IsRegularAlgebraic →
    S.isoClass.HasSupercuspidalComponent.{uE, uV} v →
    (S.determinantTwist α hα).isoClass.IsConjugateSelfDual ∧
    (S.determinantTwist α hα).isoClass.IsRegularAlgebraic ∧
    (S.determinantTwist α hα).isoClass.HasSquareIntegrableComponent.{uE, uV} v

end Langlands.Global.Harris
