import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Faithfulness of the action of an fppf quotient by the full centre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H Q G : GroupScheme S}

/-- A local lift of a quotient point, together with its fppf covering map. -/
structure FppfQuotientPointLift (q : H ⟶ Q) {T : Over S} (x : T ⟶ Q.X) where
  cover : Over S
  projection : cover ⟶ T
  lift : cover ⟶ H.X
  commutes : projection ≫ x = lift ≫ q.hom.hom
  flat : Flat projection.left
  surjective : Surjective projection.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection.left

/-- The canonical local lift is the pullback of the quotient map along the point. -/
def fppfQuotientPointLift (q : H ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {T : Over S} (x : T ⟶ Q.X) : FppfQuotientPointLift q x := by
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let b : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let h : V ⟶ H.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  refine ⟨V, b, h, Over.OverMorphism.ext pullback.condition, ?_, ?_, ?_⟩
  · change Flat (pullback.fst x.left q.hom.hom.left)
    infer_instance
  · change Surjective (pullback.fst x.left q.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation (pullback.fst x.left q.hom.hom.left)
    infer_instance

/-- Equality can be tested after locally lifting one quotient point along an
fppf homomorphism; no quasi-compactness hypothesis is needed. -/
theorem hom_ext_of_fppf_local_quotient_lift (q : H ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {T Y : Over S} (x : T ⟶ Q.X) (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (h : V ⟶ H.X),
      b ≫ x = h ≫ q.hom.hom → b ≫ f = b ≫ f') : f = f' := by
  let L := fppfQuotientPointLift q x
  let : Flat L.projection.left := L.flat
  let : Surjective L.projection.left := L.surjective
  let : LocallyOfFinitePresentation L.projection.left := L.locallyOfFinitePresentation
  have : Epi L.projection.left := inferInstance
  have : Epi L.projection := Over.epi_of_epi_left L.projection
  apply (cancel_epi L.projection).mp
  exact he L.cover L.projection L.lift L.commutes

variable {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (center G) q)
  (a : AutomorphicAction Q G)
  (ha : a.restrict q = conjugation (𝟙 G))

include ha

/-- On any lifted point, the supplied quotient action is conjugation. -/
theorem act_lift_of_restrict_eq_conjugation {T : Over S}
    (h g : T ⟶ G.X) : a.act (h ≫ q.hom.hom) g = h * g * h⁻¹ := by
  have he := congrArg (fun b : AutomorphicAction G G => b.act h g) ha
  simpa only [restrict_act, conjugation_act, Grp.id_hom_hom, Category.comp_id] using he

include hq

/-- An acting point that acts identically on every refinement is the identity. -/
theorem kernel_trivial_of_isFppfQuotient_center {T : Over S} (x : T ⟶ Q.X)
    (hx : ∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X),
      a.act (t ≫ x) g = g) : x = 1 := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  apply hom_ext_of_fppf_local_quotient_lift q x x 1
  intro V b h hb
  rw [MonObj.comp_one, hb]
  apply (mem_range_kernelι_iff q h).mp
  rw [hq.2.2.2]
  apply mem_center.mpr
  intro W t g
  have he := hx (t ≫ b) g
  rw [Category.assoc, hb, ← Category.assoc,
    act_lift_of_restrict_eq_conjugation a ha] at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- Every action of an fppf quotient by the full centre that restricts to
conjugation is faithful on all relative test schemes. -/
theorem isFaithful_of_isFppfQuotient_center : a.IsFaithful :=
  a.isFaithful_of_kernel
    (fun x hx => kernel_trivial_of_isFppfQuotient_center hq a ha x hx)

end Langlands.GroupScheme.AutomorphicAction
