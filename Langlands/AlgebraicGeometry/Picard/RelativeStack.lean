import Langlands.CategoryTheory.Sites.StackTransport
import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Stack transport for the actual relative line-bundle pseudofunctor -/

universe t u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The relative-space functor preserves covers for any topology on schemes. -/
lemma relativeSpace_coverPreserving (J : GrothendieckTopology Scheme.{u}) :
    CoverPreserving (J.over S) J (relativeSpace f) :=
  CoverPreserving.comp (J.over S) (J.over X)
    (J.coverPreserving_overPullback f) (J.over_forget_coverPreserving X)

namespace PicardGroupoid

/-- Full descent data for the actual relative groupoid are the full descent
data for the corresponding family of fibre products. -/
def relativeDescentDataEquivalence {ι : Type t} {T : Over S}
    {U : ι → Over S} (g : ∀ i, U i ⟶ T) :
    (relative f).DescentData g ≌
      pseudofunctor.DescentData (fun i ↦ (relativeSpace f).map (g i)) :=
  Langlands.CategoryTheory.StackPullback.descentDataEquivalence
    (relativeSpace f) pseudofunctor
    (fun i j ↦ Langlands.CategoryTheory.StackPullback.chosenPullback (g i) (g j))
    (fun _ _ _ ↦ Langlands.CategoryTheory.StackPullback.chosenPullback₃ _ _ _)

/-- The global stack property implies the actual relative stack property. -/
lemma relative_isStack (J : GrothendieckTopology Scheme.{u})
    [pseudofunctor.{u}.IsStack J] :
    (relative f).IsStack (J.over S) :=
  Langlands.CategoryTheory.StackPullback.isStack_reindex
    (relativeSpace f) pseudofunctor (J.over S) J (relativeSpace_coverPreserving f J)

/-- The fpqc specialization of relative stack transport. -/
lemma relative_isStack_fpqc [pseudofunctor.{u}.IsStack Scheme.fpqcTopology] :
    (relative f).IsStack (Scheme.fpqcTopology.over S) :=
  relative_isStack f Scheme.fpqcTopology

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
