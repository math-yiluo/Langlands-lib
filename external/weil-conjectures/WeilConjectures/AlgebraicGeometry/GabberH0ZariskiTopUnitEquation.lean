/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation

/-! # The top-open comparison unit equation

Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-top-unit-equation).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The explicit section comparison carries the topological unit to the etale unit.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-top-unit-equation).

Proof: Apply hbeta at the top open. Its right side is the etale unit for i'
followed by restriction along the preimage-open isomorphism. Unfold the section
comparison: first the top-open/iterated-identity pullback isomorphism, then the
unit-compatible sheaf composition isomorphism, then pullbackComp, and finally
transport along pullback.condition. Naturality of the unit with respect to the
top-open/identity isomorphism identifies the first two restrictions with the
unit applied to gabberZariskiLift. The composition-unit equation identifies
the remaining maps with etaleSetDescentComparison h i'. The last transport is
exactly pullback.condition.symm as in the statement. This does not use a
representative, a cover, or a target section; on the empty scheme the same
naturality identities apply. -/
theorem gabber_h0_zariski_top_unit_equation
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (beta : (gabberZariskiPull (pullback.snd i h)).obj (gabberZariskiG h F) ⟶
      gabberZariskiH i h F)
    (hbeta : GabberZariskiUnitCompatible i h F beta) :
    ∀ s : (gabberZariskiG h F).obj.obj (op (⊤ : X'.Opens)),
    (gabberZariskiCompare i h F ∘ beta.hom.app (op (⊤ : (pullback i h).Opens)))
      (gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) ⊤ s) =
    eqToHom (congrArg
      (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
          (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
      (etaleSetDescentComparison h (pullback.snd i h) F
        (Scheme.Etale.mk (𝟙 X)) (gabberZariskiLift h F s)) := by
  have hb : beta.hom.app (op (⊤ : (pullback i h).Opens)) ∘
      gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) ⊤ =
    (((Scheme.etaleSetPullback (pullback.snd i h)).obj
      ((Scheme.etaleSetPullback h).obj F)).obj.map
        (gabberPreimageEtaleIso (pullback.snd i h) ⊤).hom.op) ∘
    (etaleSetDescentUnit (pullback.snd i h)
      ((Scheme.etaleSetPullback h).obj F) (Scheme.Etale.mk (⊤ : X'.Opens).ι)) :=
    funext (hbeta ⊤)
  have ht := congrArg (fun f ↦ gabberZariskiCompare i h F ∘ f) hb
  have hc := gabber_h0_zariski_section_unit_equation i h F
  intro s
  exact congrFun (ht.trans hc) s

end AlgebraicGeometry
