import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Category.UniverseLift

/-! # Normalized induction across independent carrier universes -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV uW uX

open CategoryTheory
open scoped MonoidAlgebra

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- An equivalence between Levi representations, including between different
carrier universes, induces an equivalence between their actual full-parabolic
normalized induced representations. -/
def normalizedInductionEquivOfEquiv (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (e : A.representation.Equiv B.representation) :
    ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation.Equiv
      ((normalizedInductionFunctor.{uG, uW} h hU).obj B).representation :=
  Induction.smoothInducedEquiv P
    (Langlands.twistEquiv (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
      (Representation.Equiv.mk e.toLinearEquiv
        (fun p => e.isIntertwining' (h.projection p))))

/-- On induced functions the comparison is pointwise application of the
original equivalence. -/
@[simp]
theorem normalizedInductionEquivOfEquiv_eval (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (e : A.representation.Equiv B.representation)
    (f : (normalizedInductionFunctor.{uG, uV} h hU).obj A) (g : G) :
    Induction.eval P (inducingRepresentation h hU B)
      (normalizedInductionEquivOfEquiv h hU e f) g =
        e (Induction.eval P (inducingRepresentation h hU A) f g) := rfl

/-- The finite group-algebra length of normalized induction is independent
of the chosen equivalent inducing carrier. -/
theorem normalizedInduction_hasFiniteLength_iff_of_equiv
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (e : A.representation.Equiv B.representation) :
    ((normalizedInductionFunctor.{uG, uV} h hU).obj A).HasFiniteLength ↔
      ((normalizedInductionFunctor.{uG, uW} h hU).obj B).HasFiniteLength := by
  let E := normalizedInductionEquivOfEquiv h hU e
  constructor
  · intro hA
    exact IsFiniteLength.of_surjective hA
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        E.toIntertwiningMap) E.surjective
  · intro hB
    exact IsFiniteLength.of_surjective hB
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        E.symm.toIntertwiningMap) E.symm.surjective

/-- The actual comparison with normalized induction of the universe-lifted
Levi representation. -/
def normalizedInductionUniverseLiftEquiv
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation.Equiv
      ((normalizedInductionFunctor.{uG, max uV uX} h hU).obj
        (SmoothRep.universeLift.{uX} A)).representation :=
  normalizedInductionEquivOfEquiv h hU (SmoothRep.universeLiftEquiv.{uX} A)

/-- Universe lifting does not change whether the actual normalized induced
representation has finite group-algebra length. -/
theorem normalizedInduction_universeLift_hasFiniteLength_iff
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor.{uG, max uV uX} h hU).obj
      (SmoothRep.universeLift.{uX} A)).HasFiniteLength ↔
        ((normalizedInductionFunctor.{uG, uV} h hU).obj A).HasFiniteLength :=
  (normalizedInduction_hasFiniteLength_iff_of_equiv h hU
    (SmoothRep.universeLiftEquiv.{uX} A)).symm

end Langlands.Aubert.General
