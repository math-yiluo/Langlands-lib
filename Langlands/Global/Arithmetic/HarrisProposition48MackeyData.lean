import Langlands.Global.Arithmetic.HarrisProposition48ParityData

/-! # Actual child problems in the Proposition 4.8 Mackey step -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality

namespace Proposition48Problem

/-- A child uses the actual compositum and norm-pulled character, with
commuting embeddings into the parent's closure and inherited places.
No validity or existence theorem is part of this definition. -/
def IsMackeyChild (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (R : Proposition48Problem.{uF}) : Prop :=
  ∃ (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D a) (j : R.L →+* Q.L),
    R.p = Q.p ∧
    (∀ x : R.E,
      (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L)) ∧
    (∀ x : R.E',
      j (algebraMap R.E' R.L x) = (e' x : Q.L)) ∧
    Set.range (fun x : R.K₀ ↦ ((e (x : R.E) : D) : Q.L)) =
      Set.range (fun x : Q.K₀ ↦ algebraMap Q.E Q.L (x : Q.E)) ∧
    R.ξ = (Q.mackeyCharacter D a).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (ideleClassEquiv e')) ∧
    (finitePlaceEquiv e.symm R.P.v).asIdeal.LiesOver Q.P.v.asIdeal ∧
    (finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal

end Proposition48Problem

end Langlands.Global.Harris
