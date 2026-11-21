import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.HeckeCharacterTransport
import Langlands.Galois.AlgebraicHeckeMonomialStatement

/-! # Local arithmetic separation of prime-orbit Mackey constituents -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.GaloisRepresentation AdelicFunctoriality NumberField

/-- The prime orbit separates the actual finite characters in degree one
and the actual local restrictions of commonly corrected monomial avatars
at a coefficient place away from the auxiliary residue characteristic. -/
def Proposition48PrimeMackeyLocalSeparationStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L) [IsGalois Q.E D],
    Q.IsAuxiliaryValid → D ≤ Q.conjugateField 1 →
    ∀ (w : FinitePlacesAbove D Q.Ps.v) (a b : Q.L ≃ₐ[Q.E] Q.L),
      AlgEquiv.restrictNormalHom D a ≠ AlgEquiv.restrictNormalHom D b →
      let A := Q.mackeyField D a
      let B := Q.mackeyField D b
      letI : Algebra D A :=
        (IntermediateField.inclusion (show D ≤ A from le_sup_left)).toAlgebra
      letI : Algebra D B :=
        (IntermediateField.inclusion (show D ≤ B from le_sup_left)).toAlgebra
      (∀ (ea : D ≃ₐ[D] A) (eb : D ≃ₐ[D] B),
        (HeckeCharacter.comap ea.toRingEquiv (Q.mackeyCharacter D a)).finiteComponent w.1 ≠
          (HeckeCharacter.comap eb.toRingEquiv (Q.mackeyCharacter D b)).finiteComponent w.1) ∧
      ∀ (ν : HeckeCharacter D) (r : ℕ),
        let χa := algebraicNormTwist r
          (Q.mackeyCharacter D a * ν.comp (ideleClassNorm (K := D) (L := A)))
        let χb := algebraicNormTwist r
          (Q.mackeyCharacter D b * ν.comp (ideleClassNorm (K := D) (L := B)))
        ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ) (lam : FinitePlace L),
          residueCharacteristic w.1 ≠ residueCharacteristic lam →
          ∀ (ψa : LambdaAdicCharacter A L lam) (ψb : LambdaAdicCharacter B L lam)
            (Ra Rb : LambdaAdic.{0, 0, uV} D L lam),
            (∀ wa : FinitePlacesAbove A w.1, IsLocalLambdaAdicRealization ι lam χa ψa wa.1) →
            (∀ wb : FinitePlacesAbove B w.1, IsLocalLambdaAdicRealization ι lam χb ψb wb.1) →
            IsInducedFromLambdaAdicCharacter (algebraMap D A) lam ψa Ra →
            IsInducedFromLambdaAdicCharacter (algebraMap D B) lam ψb Rb →
              ¬ Nonempty (FiniteRepresentation.Equiv
                (atFinitePlace w.1 Ra).val (atFinitePlace w.1 Rb).val)

end Langlands.Global.Harris
