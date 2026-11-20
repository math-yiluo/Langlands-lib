import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.HeckeCharacterTransport

/-! # Arithmetic transport of the corrected Mackey child -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Global.AdelicFunctoriality

/-- Pull back both actual child realizations and the correcting character by
the same base isomorphism. The correction still acts through the determinant,
its inducing character still uses the norm pullback, and the corrected child
keeps its regular algebraicity. -/
def Proposition48CorrectedChildTransportStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L) (R : Proposition48Problem.{uF})
    (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D a),
    (∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L)) →
    R.ξ = HeckeCharacter.comap e' (Q.mackeyCharacter D a) →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    letI : Algebra D (Q.mackeyField D a) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
    ∀ (ν : HeckeCharacter R.E) (r : ℕ) (S T : CuspidalOperatorRealization R.E r),
      T.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} (R.correctedCharacter ν) →
      T.isoClass.IsRegularAlgebraic →
      OperatorRealization.IsDeterminantMultiple ν S.realization T.realization →
      let ω := HeckeCharacter.comap e.symm ν
      let S' := S.arithmeticComap e.symm
      let T' := T.arithmeticComap e.symm
      T'.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV}
        (Q.mackeyCharacter D a * ω.comp (ideleClassNorm (K := D) (L := Q.mackeyField D a))) ∧
        T'.isoClass.IsRegularAlgebraic ∧
        OperatorRealization.IsDeterminantMultiple ω S'.realization T'.realization

end Langlands.Global.Harris
