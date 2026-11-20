import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.HeckeCharacterTransport

/-! # Arithmetic basepoint of the prime Mackey orbit -/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality

/-- The transports of the identity Mackey child used at the chosen auxiliary
place. The base and inducing-field maps intertwine the embeddings, and the
inducing character and auxiliary place are transported by those same maps. -/
def Proposition48Problem.IsPrimeOrbitBasepoint (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (R : Proposition48Problem.{uF})
    (w : FinitePlacesAbove D Q.Ps.v) (e : R.E ≃+* D)
    (e' : R.E' ≃+* Q.mackeyField D 1) : Prop :=
  (∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L)) ∧
    R.ξ = HeckeCharacter.comap e' (Q.mackeyCharacter D 1) ∧
    finitePlaceEquiv e.symm R.Ps.v = w.1

/-- The witness of the identity Mackey child yields a basepoint at the unique
place above the parent's auxiliary place. -/
def Proposition48PrimeOrbitBasepointStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (R : Proposition48Problem.{uF}) (w : FinitePlacesAbove D Q.Ps.v),
    (∀ z : FinitePlacesAbove D Q.Ps.v, z = w) → Q.IsAuxiliaryMackeyChild D 1 R →
      ∃ (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D 1),
        Q.IsPrimeOrbitBasepoint D R w e e'

end Langlands.Global.Harris
