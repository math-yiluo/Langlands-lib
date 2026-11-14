import Langlands.Global.Arithmetic.HarrisProposition48Statement
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.DoubleCoset

/-!
# Concrete data for the induction in Harris's Proposition 4.8

The fields in this interface are small; the local field and local factor
carriers retain independent universes. No existence or induction theorem is
asserted here.
-/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure
open AdelicFunctoriality

/-- A bundled instance of the existing Proposition 4.8 problem over small
number fields. The scalar tower is already a conjunct of the existing datum. -/
structure Proposition48Problem where
  p : ℕ
  [prime : Fact p.Prime]
  F : PadicField.{uF} p
  F' : Extension F
  E : Type
  E' : Type
  L : Type
  [fieldE : Field E]
  [numberFieldE : NumberField E]
  [fieldE' : Field E']
  [numberFieldE' : NumberField E']
  [fieldL : Field L]
  [numberFieldL : NumberField L]
  [algebraEE' : Algebra E E']
  [algebraEL : Algebra E L]
  [algebraE'L : Algebra E' L]
  [scalarTower : IsScalarTower E E' L]
  [cmE : IsCMField E]
  [cmE' : IsCMField E']
  [compact : CompactSpace (AdeleQuotient E)]
  e : ReciprocityFamily F
  χ : FieldCharacter F F'
  χs : FieldCharacter F F'
  K₀ : IntermediateField ℚ E
  P : PlaceDatum F F' E E' L
  Ps : PlaceDatum F F' E E' L
  ξ : HeckeCharacter E'

attribute [instance] Proposition48Problem.prime
  Proposition48Problem.fieldE Proposition48Problem.numberFieldE
  Proposition48Problem.fieldE' Proposition48Problem.numberFieldE'
  Proposition48Problem.fieldL Proposition48Problem.numberFieldL
  Proposition48Problem.algebraEE' Proposition48Problem.algebraEL
  Proposition48Problem.algebraE'L Proposition48Problem.scalarTower
  Proposition48Problem.cmE Proposition48Problem.cmE' Proposition48Problem.compact

namespace Proposition48Problem

/-- Exactly the two premises of the published proposition. -/
def IsValid (Q : Proposition48Problem.{uF}) : Prop :=
  NormalizedReciprocity Q.F Q.e ∧
    IsProposition48Datum Q.e Q.χ Q.χs Q.K₀ Q.P Q.Ps Q.ξ

/-- Exactly its four-part existential conclusion. -/
def HasSolution (Q : Proposition48Problem.{uF}) : Prop :=
  ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    c.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ ∧
    c.IsRegularAlgebraic ∧ c.IsConjugateSelfDual ∧
    c.HasSupercuspidalComponent.{0, uV} Q.Ps.v

/-- The normal-closure degree used for strong induction, not the rank of
an individual Mackey constituent. -/
def inductionDegree (Q : Proposition48Problem.{uF}) : ℕ :=
  Module.finrank Q.E Q.L

/-- The actual embedding of `E'` into `L`, followed by `a`. -/
def conjugateEmbedding (Q : Proposition48Problem.{uF}) (a : Q.L ≃ₐ[Q.E] Q.L) :
    Q.E' →ₐ[Q.E] Q.L :=
  a.toAlgHom.comp (IsScalarTower.toAlgHom Q.E Q.E' Q.L)

/-- The subfield `a(E')` of the common normal closure. -/
def conjugateField (Q : Proposition48Problem.{uF}) (a : Q.L ≃ₐ[Q.E] Q.L) :
    IntermediateField Q.E Q.L :=
  (Q.conjugateEmbedding a).fieldRange

/-- The compositum `D · a(E')` inside `L`. -/
def mackeyField (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L) : IntermediateField Q.E Q.L :=
  D ⊔ Q.conjugateField a

/-- Harris's rank `n(a,i) = [a(E')E_i : E_i]`. -/
def mackeyRank (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L) : ℕ :=
  letI : Algebra D (Q.mackeyField D a) :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
  Module.finrank D (Q.mackeyField D a)

/-- The transported character `a(ξ)` on the actual copy `a(E')`. -/
def conjugateCharacter (Q : Proposition48Problem.{uF}) (a : Q.L ≃ₐ[Q.E] Q.L) :
    HeckeCharacter (Q.conjugateField a) :=
  Q.ξ.comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (ideleClassEquiv (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv).symm)

/-- The unmodified Mackey inducing character
`a(ξ) ∘ N_{D·a(E')/a(E')}`. No parity correction is silently inserted. -/
def mackeyCharacter (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L) : HeckeCharacter (Q.mackeyField D a) :=
  letI : Algebra (Q.conjugateField a) (Q.mackeyField D a) :=
    (IntermediateField.inclusion
      (show Q.conjugateField a ≤ Q.mackeyField D a from le_sup_right)).toAlgebra
  (Q.conjugateCharacter a).comp
    (ideleClassNorm (K := Q.conjugateField a) (L := Q.mackeyField D a))

/-- Double cosets `Gal(L/D) \ Gal(L/E) / Gal(L/E')`. Inversion identifies
this indexing with Harris's opposite-order convention. -/
def MackeyIndex (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L) : Type :=
  DoubleCoset.Quotient (D.fixingSubgroup : Set (Q.L ≃ₐ[Q.E] Q.L))
    ((Q.conjugateField 1).fixingSubgroup : Set (Q.L ≃ₐ[Q.E] Q.L))

/-- The prime cyclic final step of Harris's tower. -/
def IsPrimeCyclicStep (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) : Prop :=
  IsGalois Q.E D ∧ IsCyclic (D ≃ₐ[Q.E] D) ∧ (Module.finrank Q.E D).Prime

end Proposition48Problem

end Langlands.Global.Harris
