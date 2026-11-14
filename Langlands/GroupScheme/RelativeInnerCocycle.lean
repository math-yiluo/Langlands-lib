import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-! # Faithful central-quotient actions and their inner discrepancy cocycles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {G A : GroupScheme S}

/-- Equality can be checked after locally lifting a point along an fppf homomorphism.
No quasi-compactness of the homomorphism or affineness of the groups is required. -/
theorem hom_ext_of_fppf_quotient_lift (p : G ⟶ A)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [LocallyOfFinitePresentation p.hom.hom.left]
    {T Y : Over S} (x : T ⟶ A.X) (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (g : V ⟶ G.X),
      b ≫ x = g ≫ p.hom.hom → b ≫ f = b ≫ f') : f = f' := by
  let V : Over S := Over.mk (pullback.fst x.left p.hom.hom.left ≫ T.hom)
  let b : V ⟶ T := Over.homMk (pullback.fst x.left p.hom.hom.left) rfl
  let g : V ⟶ G.X := Over.homMk (pullback.snd x.left p.hom.hom.left) (by
    rw [← Over.w p.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have : Epi b.left := by
    change Epi (pullback.fst x.left p.hom.hom.left)
    infer_instance
  have : Epi b := Over.epi_of_epi_left b
  apply (cancel_epi b).mp
  exact he V b g (Over.OverMorphism.ext pullback.condition)

variable (p : G ⟶ A) (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction A G)
    (hc : c.restrict p = conjugation (𝟙 G))

include hc in
/-- The action of a quotient point with a lift is conjugation by that lift. -/
theorem centralQuotient_act_lift {T : Over S} (g y : T ⟶ G.X) :
    c.act (g ≫ p.hom.hom) y = g * y * g⁻¹ := by
  have h := congrArg (fun a : AutomorphicAction G G => a.act g y) hc
  simpa only [restrict_act, conjugation_act, Grp.id_hom_hom, Category.comp_id] using h

include hp hc in
/-- The all-refinement kernel of the specified central-quotient action is trivial. -/
theorem centralQuotient_action_kernel {T : Over S} (x : T ⟶ A.X)
    (hx : ∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X),
      c.act (t ≫ x) g = g) : x = 1 := by
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  let : LocallyOfFinitePresentation p.hom.hom.left := hp.2.2.1
  apply hom_ext_of_fppf_quotient_lift p x x 1
  intro V b g hb
  rw [MonObj.comp_one, hb]
  apply (mem_range_kernelι_iff p g).mp
  rw [hp.2.2.2]
  intro W t y
  have h := hx (t ≫ b) y
  rw [Category.assoc, hb, ← Category.assoc, centralQuotient_act_lift p c hc] at h
  exact mul_inv_eq_iff_eq_mul.mp h

include hp hc in
/-- An action whose restriction is conjugation along the quotient by the full centre is
faithful on all scheme tests. -/
theorem centralQuotient_action_isFaithful : c.IsFaithful :=
  c.isFaithful_of_kernel (fun x hx => centralQuotient_action_kernel p hp c hc x hx)

end AutomorphicAction

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}
    (e : LocalGroupIso G H U) (p : G ⟶ A)
    (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction A G)
    (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 G))
    (he : e.HasInnerDiscrepancy c)

/-- The natural discrepancy cocycle for the supplied quotient by the centre.
Pointwise innerness supplies the values; faithfulness proves their naturality and laws. -/
def innerCocycleOfCentralQuotient : Cocycle A U :=
  e.innerCocycle c (c.centralQuotient_action_isFaithful p hp hc) he

/-- The constructed cocycle represents the original local family's discrepancy. -/
theorem innerCocycleOfCentralQuotient_hasDiscrepancy :
    e.HasDiscrepancy c (e.innerCocycleOfCentralQuotient p hp c hc he) :=
  e.innerCocycle_hasDiscrepancy c (c.centralQuotient_action_isFaithful p hp hc) he

end LocalGroupIso

end Langlands.GroupScheme
