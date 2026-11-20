import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Galois.Harris1998ExistenceStatement
import Langlands.Galois.PureFrobeniusWeightAlignmentStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Global.Arithmetic.HarrisProposition48SingletonMonomialStatement

/-! # Finite untwisting and extension matching in Harris's Lemma 1.6 -/

noncomputable section

universe uF uE uL uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

open Langlands.Global Langlands.GaloisRepresentation

/-- The family output of the cuspidal form of Harris's Theorem 1.2, on a
specified class. -/
def HasWeaklyAssociatedPureFamily {E : Type uE} [Field E] [NumberField E]
    [CompactSpace (AdeleQuotient E)] {r : ℕ} (c : IsoClass E r) : Prop :=
  ∃ (L : Type uL) (fieldL : Field L),
    letI : Field L := fieldL
    ∃ (numberFieldL : NumberField L),
      letI : NumberField L := numberFieldL
      ∃ (ι : L →+* ℂ) (excluded : Finset (FinitePlace L)) (m : ℕ)
        (R : Fin m → Collection.{uE, uL, uV} E L excluded)
        (w : Fin m → ℤ) (d : Fin m → ℕ),
        (∀ k, IsPureCompatible excluded (R k) (w k)) ∧
        (∀ k, HasRank excluded (R k) (d k)) ∧
        ∑ k, d k = r + 1 ∧ c.IsSumWeaklyAssociated.{uE, uL, uV, uW} ι excluded R

end Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.GaloisRepresentation
open Langlands.FiniteRepresentation

/-- A compatible pure-family sum for an actual finite-order determinant twist
untwists to a compatible pure-family sum for the original cuspidal class. -/
def FiniteOrderWeakAssociationUntwistStatement : Prop :=
  AlgebraicHeckeLambdaAdicRealizationStatement.{uE, uL} →
  ∀ (E : Type uE) [Field E] [NumberField E] [NumberField.IsCMField E]
    [CompactSpace (AdeleQuotient E)] (r : ℕ) (S : CuspidalOperatorRealization E r)
    (α : HeckeCharacter E) (hα : α.HasFiniteOrder),
    (S.determinantTwist α hα).isoClass.HasWeaklyAssociatedPureFamily.{uE, uL, uV, uW} →
    S.isoClass.HasWeaklyAssociatedPureFamily.{uE, uL, uV, uW}

/-- After a pure-family sum for one weak descent has been constructed, match
its cyclic twists to extensions of the irreducible restricted monomial
family and select the one giving the original inducing character. -/
def Proposition48SingletonExtensionMatchingTCStatement : Prop :=
  AlgebraicHeckeLambdaAdicRealizationStatement.{0, 0} →
  HeckeCharacterGaloisInductionStatement.{0, 0, 0} →
  Proposition48SingletonMonomialRestrictionStatement.{uF} →
  PureFrobeniusWeightAlignmentStatement.{0, 0, uV} →
  CyclicExtensionTwistClassificationStatement.{0, 0, uV, 0} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ (r : ℕ) (T : CuspidalOperatorRealization D r)
      (c : CuspidalOperatorRealization.IsoClass Q.E r) (η : HeckeCharacter Q.E),
      η.HasNormKernel D → Q.IsMackeyConstituent.{uF, uV} D 1 T.isoClass →
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV} T.isoClass c →
      c.HasWeaklyAssociatedPureFamily.{0, 0, uV, uV} →
      (∀ i : Fin (Module.finrank Q.E D), ∃ d : CuspidalOperatorRealization.IsoClass Q.E r,
        c.IsFiniteOrderDeterminantTwist (η ^ (i : ℕ)) d) →
      (∀ (i j : Fin (Module.finrank Q.E D)) (d : CuspidalOperatorRealization.IsoClass Q.E r),
        c.IsFiniteOrderDeterminantTwist (η ^ (i : ℕ)) d →
        c.IsFiniteOrderDeterminantTwist (η ^ (j : ℕ)) d → i = j) →
      ∃! i : Fin (Module.finrank Q.E D), ∃ d : CuspidalOperatorRealization.IsoClass Q.E r,
        c.IsFiniteOrderDeterminantTwist (η ^ (i : ℕ)) d ∧
        d.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ

end Langlands.Global.Harris
