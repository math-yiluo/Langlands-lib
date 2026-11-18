import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerData
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.Automorphic.AssociatedFactorStatement

/-!
# Complex-place parameters and distinct Mackey components in Proposition 4.8

Definitions for the exact-stabilizer form of the induction for Harris (1998),
Proposition 4.8. A solution carries the complex-place parameters of the
induced representation of `ξ`, as a list up to order at every complex place
of `E`. A prime cyclic step has distinct Mackey components when two cuspidal
classes over the step field, weakly induced from the characters of two
different double cosets, have different components at every place above the
auxiliary place. No existence, distinctness or compatibility is asserted.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.LocalFactor.Archimedean AdelicFunctoriality

namespace Proposition48Problem

/-- The list `ds` is, up to order, the parameter at the complex place `v` of `E`
of the representation induced from `ξ`. There are actual parameters `dξ w` of
`ξ` at the places `w` of `E'` above `v`, and `ds` is a permutation of their
concatenation, each read in the coordinates of `v`, in the order of some
enumeration `e` of these places. -/
def IsInducedComplexPlaceParameter (Q : Proposition48Problem.{uF})
    (v : {v : InfinitePlace Q.E // v.IsComplex}) (ds : List ComplexCharacterData) :
    Prop :=
  ∃ (d : ℕ) (e : Fin d ≃ InfinitePlacesAbove Q.E' v.1)
    (dξ : InfinitePlacesAbove Q.E' v.1 → ComplexCharacterData),
    (∀ w, Q.ξ.HasComplexPlaceParameter (complexPlaceAbove v w) (dξ w)) ∧
      ds.Perm (complexPlaceLanglandsSum v e fun w => [dξ w])

/-- At every complex place of `E`, the cuspidal class `c` has an actual
parameter that is the parameter of the representation induced from `ξ`. -/
def HasInducedComplexPlaceParameters (Q : Proposition48Problem.{uF}) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass Q.E r) : Prop :=
  ∀ v : {v : InfinitePlace Q.E // v.IsComplex},
    ∃ ds : List ComplexCharacterData,
      c.HasComplexPlaceParameter v ds ∧ Q.IsInducedComplexPlaceParameter v ds

/-- A solution in the sense of `IsSolution` that also has the complex-place
parameters of the representation induced from `ξ`. -/
def HasParameterSolution (Q : Proposition48Problem.{uF}) : Prop :=
  ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    Q.IsSolution.{uF, uV} c ∧ Q.HasInducedComplexPlaceParameters c

/-- The cuspidal class `c` over the intermediate field `D` is a weak automorphic
induction of the Mackey character `a(ξ) ∘ N` of `D · a(E')`. -/
def IsMackeyConstituent (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    [CompactSpace (AdeleQuotient D)] {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass D r) : Prop :=
  letI : Algebra D (Q.mackeyField D a) :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
  c.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.mackeyCharacter D a)

/-- Mackey constituents of different double cosets have different local
components above the auxiliary place. For `a`, `a'` in different classes of
`Gal(L/D) \ Gal(L/E) / Gal(L/E')`, and cuspidal realizations `T`, `U` of the same
`GL_(r+1)` over `D` with unitary central characters, weakly induced from the
Mackey characters of `a` and `a'`, the components of any spectral presentations
of `T` and `U` at every place of `D` above `Ps.v` are not isomorphic. -/
def HasDistinctMackeyComponents (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) : Prop :=
  letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  ∀ a a' : Q.L ≃ₐ[Q.E] Q.L,
    DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a ≠
      DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a' →
    ∀ (r : ℕ) (T U : CuspidalOperatorRealization D r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter U →
      Q.IsMackeyConstituent.{uF, uV} D a T.isoClass →
      Q.IsMackeyConstituent.{uF, uV} D a' U.isoClass →
      ∀ (w : FinitePlacesAbove D Q.Ps.v)
        (P : CuspidalSpectralPresentation.{0, uV} T)
        (P' : CuspidalSpectralPresentation.{0, uV} U),
        (P.localComponent w.1).isoClass ≠ (P'.localComponent w.1).isoClass

end Proposition48Problem

end Langlands.Global.Harris
