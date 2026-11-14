import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Descent of stability through a cover of the acting group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H H' G K : GroupScheme B}
    (a : AutomorphicAction H' G) (t : H ⟶ H')
    [Flat t.hom.hom.left] [Surjective t.hom.hom.left]
    [LocallyOfFinitePresentation t.hom.hom.left]
    {F : SubgroupFunctor G} {i : K ⟶ G} (hi : F.IsRepresentedBy i)

include hi

/-- Stability of a represented subgroup descends through a flat surjective
locally finitely presented change of acting group, on every scheme test. -/
theorem isStable_of_restrict (h : (a.restrict t).IsStable F) : a.IsStable F := by
  let : Mono i.hom.hom := hi.1
  intro U s x hx
  let V : Over B := Over.mk (pullback.fst s.left t.hom.hom.left ≫ U.hom)
  let c : V ⟶ U := Over.homMk (pullback.fst s.left t.hom.hom.left) rfl
  let z : V ⟶ H.X := Over.homMk (pullback.snd s.left t.hom.hom.left) (by
    rw [← Over.w t.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w s]
    rfl)
  have hcs : c ≫ s = z ≫ t.hom.hom := Over.OverMorphism.ext pullback.condition
  have : Flat c.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective c.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation c.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  rw [← hi.2]
  apply SubgroupFunctor.mem_range_of_comp_mem_range i c
  rw [hi.2, a.naturality, hcs, ← restrict_act]
  exact h V z (c ≫ x) (F.comp_mem c hx)

/-- Restriction along an actual fppf cover preserves and reflects stability
of a represented subgroup. -/
theorem isStable_restrict_iff : (a.restrict t).IsStable F ↔ a.IsStable F := by
  constructor
  · exact isStable_of_restrict a t hi
  · intro h U s x hx
    simpa only [restrict_act] using h U (s ≫ t.hom.hom) x hx

/-- Restrict the whole action to a represented subgroup using stability checked
only after the supplied cover of the acting group. -/
def onRepresentedSubgroupOfStableRestriction (h : (a.restrict t).IsStable F) :
    AutomorphicAction H' K :=
  a.onRepresentedSubgroup i hi (isStable_of_restrict a t hi h)

end Langlands.GroupScheme.AutomorphicAction
