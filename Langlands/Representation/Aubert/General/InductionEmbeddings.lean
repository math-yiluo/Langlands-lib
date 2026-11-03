import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Induction.Equivalences

/-! # Embeddings under actual normalized induction across carrier universes -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV uW

open CategoryTheory

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- Postcomposition on full-parabolic normalized induced functions, allowing
the coefficient representations to have independent carrier universes. -/
def normalizedInductionMap (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (f : A.representation.IntertwiningMap B.representation) :
    ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation.IntertwiningMap
      ((normalizedInductionFunctor.{uG, uW} h hU).obj B).representation :=
  Induction.smoothInducedMap P
    (Langlands.twistIntertwining
      (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
      { toLinearMap := f.toLinearMap
        isIntertwining' p := f.isIntertwining' (h.projection p) })

/-- The induced map applies the original coefficient map at every argument. -/
@[simp]
theorem normalizedInductionMap_eval (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (f : A.representation.IntertwiningMap B.representation)
    (v : (normalizedInductionFunctor.{uG, uV} h hU).obj A) (g : G) :
    Induction.eval P (inducingRepresentation h hU B)
      (normalizedInductionMap h hU f v) g =
        f (Induction.eval P (inducingRepresentation h hU A) v g) := rfl

/-- In a fixed carrier universe the map is exactly the published functor map. -/
@[simp]
theorem normalizedInductionMap_hom (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    {A B : SmoothRep.{0, uG, uV} ℂ M} (f : A ⟶ B) :
    normalizedInductionMap h hU (SmoothRep.hom f) =
      SmoothRep.hom ((normalizedInductionFunctor h hU).map f) := rfl

/-- Actual normalized induction preserves injectivity of coefficient maps
even when their carriers lie in different universes. -/
theorem normalizedInductionMap_injective (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (f : A.representation.IntertwiningMap B.representation)
    (hf : Function.Injective f) :
    Function.Injective (normalizedInductionMap h hU f) :=
  Induction.smoothInducedMap_injective P _ hf

/-- An embedding of coefficients lets finite group-algebra length descend
from the target's normalized induction to the source's normalized induction. -/
theorem normalizedInduction_hasFiniteLength_of_injective
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (f : A.representation.IntertwiningMap B.representation)
    (hf : Function.Injective f)
    (hB : ((normalizedInductionFunctor.{uG, uW} h hU).obj B).HasFiniteLength) :
    ((normalizedInductionFunctor.{uG, uV} h hU).obj A).HasFiniteLength :=
  IsFiniteLength.of_injective hB
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (normalizedInductionMap h hU f))
    (normalizedInductionMap_injective h hU f hf)

end Langlands.Aubert.General
