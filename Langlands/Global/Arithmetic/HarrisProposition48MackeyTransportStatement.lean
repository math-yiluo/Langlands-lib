import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.CuspidalComplexParameterBridgeStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement

/-!
# Mackey constituents, child transport and induced parameters in Proposition 4.8

Statements only, for the Mackey step of the induction for Harris (1998),
Proposition 4.8 (proof, printed pp.202–203), in the form where solutions carry
complex-place parameters. They are the arithmetic and automorphic interfaces
between the children of a prime cyclic step `D` and the parent problem:

* the double cosets of a step with `[D : E]` Mackey classes are the fibres of
  restriction to `D`, and then `D ⊆ E'`;
* a Galois conjugate of a Mackey constituent is a Mackey constituent;
* the untwisted constituent of a child over `R.E` moves to `D` along the
  child's field isomorphisms, as a Mackey constituent with the induced
  complex-place parameters over `D`;
* induced parameters and weak induction compose in stages `E ⊆ D ⊆ E'`;
* the induced parameters are Clozel regular algebraic, so a class with them is
  regular algebraic once the archimedean bridge holds;
* a weak automorphic induction of a conjugate-inverse character is conjugate
  self-dual, given spectral rigidity.

No existence, transport or compatibility theorem is proved here.
-/

noncomputable section

universe uF uV uE uE'

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.LocalFactor.Archimedean AdelicFunctoriality

/-- In a prime cyclic step `D` of a problem whose `L` is the normal closure of
`E'/E`, if there are `[D : E]` Mackey classes then `D ⊆ E'` (inside `L`), and two
elements of `Gal(L/E)` lie in the same class of
`Gal(L/D) \ Gal(L/E) / Gal(L/E')` exactly when they agree on `D`. -/
def Proposition48MackeyFibreStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    IsNormalClosure Q.E Q.E' Q.L → Q.IsPrimeCyclicStep D →
    Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
    D ≤ Q.conjugateField 1 ∧
      ∀ a b : Q.L ≃ₐ[Q.E] Q.L,
        (DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a =
            DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup b ↔
          ∀ x ∈ D, a x = b x)

/-- Galois conjugation moves Mackey constituents between double cosets: if the
cuspidal class `c` over `D` is weakly induced from the Mackey character of `a`,
and `τ ∈ Gal(L/E)` restricts to `σ ∈ Gal(D/E)`, then the conjugate class
`galoisConj σ c` is weakly induced from the Mackey character of `τ * a`. -/
def Proposition48MackeyConstituentGaloisConjugateStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ (a τ : Q.L ≃ₐ[Q.E] Q.L) (σ : D ≃ₐ[Q.E] D),
      (∀ x : D, ((σ x : D) : Q.L) = τ x) →
      ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass D r),
        Q.IsMackeyConstituent.{uF, uV} D a c →
          Q.IsMackeyConstituent.{uF, uV} D (τ * a)
            (CuspidalOperatorRealization.IsoClass.galoisConj σ c)

/-- Transport of a child's constituent to the step field. Let `e : R.E ≃+* D`
and `e' : R.E' ≃+* D · a(E')` be compatible field isomorphisms identifying the
child's character `R.ξ` with the Mackey character of `a`, as in
`IsMackeyChild`. For a cuspidal realization `S` over `R.E`, its pullback
`S.arithmeticComap e.symm` over `D`
* is a Mackey constituent of `a` when `S` weakly induces `R.ξ`;
* has, at every complex place `u` of `D`, the parameter of the representation
  induced from the Mackey character, when `S` has the induced complex-place
  parameters of `R`: a list that is, up to order, the Langlands sum over the
  places of `D · a(E')` above `u` of the parameters of the Mackey character. -/
def Proposition48MackeyChildTransportStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (R : Proposition48Problem.{uF}) (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D a),
    (∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L)) →
    R.ξ = (Q.mackeyCharacter D a).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (ideleClassEquiv e')) →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    letI : Algebra D (Q.mackeyField D a) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
    ∀ (r : ℕ) (S : CuspidalOperatorRealization R.E r),
      (S.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} R.ξ →
        Q.IsMackeyConstituent.{uF, uV} D a (S.arithmeticComap e.symm).isoClass) ∧
      (R.HasInducedComplexPlaceParameters S.isoClass →
        ∀ u : {u : InfinitePlace D // u.IsComplex}, ∃ ds : List ComplexCharacterData,
          (S.arithmeticComap e.symm).isoClass.HasComplexPlaceParameter u ds ∧
          ∃ (d : ℕ) (en : Fin d ≃ InfinitePlacesAbove (Q.mackeyField D a) u.1)
            (dχ : InfinitePlacesAbove (Q.mackeyField D a) u.1 → ComplexCharacterData),
            (∀ w, (Q.mackeyCharacter D a).HasComplexPlaceParameter
              (complexPlaceAbove u w) (dχ w)) ∧
            ds.Perm (complexPlaceLanglandsSum u en fun w => [dχ w]))

/-- Induced parameters in stages for the trivial double coset of a step with
`D ⊆ E'`. Let `ds w` be, at every place `w` of `D` above the complex place `v`
of `E`, a list that is up to order the Langlands sum over the places of
`D · E'` above `w` of the parameters of the Mackey character of `1`. Then the
Langlands sum of the lists `ds w` over the places of `D` above `v`, in any
enumeration, is the parameter at `v` of the representation induced from `ξ`. -/
def Proposition48PrimeInducedParameterStagesStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    D ≤ Q.conjugateField 1 →
    letI : Algebra D (Q.mackeyField D 1) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D 1 from le_sup_left)).toAlgebra
    ∀ (v : {v : InfinitePlace Q.E // v.IsComplex}) (d : ℕ)
      (en : Fin d ≃ InfinitePlacesAbove D v.1)
      (ds : InfinitePlacesAbove D v.1 → List ComplexCharacterData),
      (∀ w : InfinitePlacesAbove D v.1,
        ∃ (d' : ℕ) (en' : Fin d' ≃ InfinitePlacesAbove (Q.mackeyField D 1)
            (complexPlaceAbove v w).1)
          (dχ : InfinitePlacesAbove (Q.mackeyField D 1) (complexPlaceAbove v w).1 →
            ComplexCharacterData),
          (∀ u, (Q.mackeyCharacter D 1).HasComplexPlaceParameter
            (complexPlaceAbove (complexPlaceAbove v w) u) (dχ u)) ∧
          (ds w).Perm
            (complexPlaceLanglandsSum (complexPlaceAbove v w) en' fun u => [dχ u])) →
      Q.IsInducedComplexPlaceParameter v (complexPlaceLanglandsSum v en ds)

/-- Weak induction in stages for the trivial double coset of a step with
`D ⊆ E'`: a cuspidal class over `E` that is a weak induction of a Mackey
constituent of `1` over `D` is a weak automorphic induction of `ξ`. -/
def Proposition48PrimeInductionStagesStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    D ≤ Q.conjugateField 1 →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ (r m : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r)
      (d : CuspidalOperatorRealization.IsoClass D m),
      CuspidalOperatorRealization.IsoClass.IsWeakInductionOf.{0, 0, uV, uV} c d →
      Q.IsMackeyConstituent.{uF, uV} D 1 d →
      c.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ

/-- Regular algebraicity from the induced parameters. Given the archimedean
bridge, if `ξ` is algebraic after the twist of parity `[E' : E] - 1`,
relatively regular and conjugate inverse, then every cuspidal class over `E`
with the complex-place parameters of the representation induced from `ξ` is
regular algebraic. -/
def Proposition48InducedParameterRegularAlgebraicStatement : Prop :=
  CuspidalComplexParameterBridgeTCStatement.{0} →
  ∀ (Q : Proposition48Problem.{uF}),
    IsAlgebraicAfterTwist (Module.finrank Q.E Q.E' - 1) Q.ξ →
    IsRelativelyRegular Q.E Q.ξ → IsConjugateInverse Q.ξ →
    ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
      Q.HasInducedComplexPlaceParameters c → c.IsRegularAlgebraic

/-- Given spectral rigidity: over a CM field `E`, a cuspidal class that is a weak
automorphic induction of a conjugate-inverse Hecke character of a CM extension
`E'` is conjugate self-dual. -/
def WeakInductionConjugateInverseSelfDualStatement : Prop :=
  CuspidalSpectralRigidityStatement.{uE, uV} →
  ∀ (E : Type uE) (E' : Type uE') [Field E] [NumberField E] [IsCMField E]
    [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E']
    [CompactSpace (AdeleQuotient E)] (ξ : HeckeCharacter E') (r : ℕ)
    (c : CuspidalOperatorRealization.IsoClass E r),
    IsConjugateInverse ξ → c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ →
      c.IsConjugateSelfDual

/-- The form of `WeakInductionConjugateInverseSelfDualStatement` whose rigidity
premise is the totally complex form `CuspidalSpectralRigidityTCStatement`; the
conclusion is unchanged (CM fields are totally complex). -/
def WeakInductionConjugateInverseSelfDualTCStatement : Prop :=
  CuspidalSpectralRigidityTCStatement.{uE, uV} →
  ∀ (E : Type uE) (E' : Type uE') [Field E] [NumberField E] [IsCMField E]
    [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E']
    [CompactSpace (AdeleQuotient E)] (ξ : HeckeCharacter E') (r : ℕ)
    (c : CuspidalOperatorRealization.IsoClass E r),
    IsConjugateInverse ξ → c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ →
      c.IsConjugateSelfDual

end Langlands.Global.Harris
