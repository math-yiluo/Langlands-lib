/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Limits

import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # The pullback adjunction unit on an isomorphism locus

Source: Stacks Project, Tags 0095 and 088B.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The unit of any tensor-pullback adjunction restricts to an isomorphism on
an open over which the scheme morphism is an isomorphism.

Source: Stacks Project, Tag 0095 (pullback adjunction), and Tag 088B, proof,
the adjunction morphism over the complement of the exceptional locus.
(blueprint: lem-weil-pbc-tensor-pullback-unit-restriction-iso)

Proof: Let j be the open inclusion and let p' be the base change of p to that
open. Restriction commutes with pushforward and with pullback, and transports
the restricted unit to the unit of p'. Since p' is an isomorphism, its pullback
and pushforward are inverse equivalences, so its unit is invertible. These
identifications hold for the standard adjunction. For any other adjunction of
the same functors, uniqueness of left adjoints changes its unit by pushforward
of a natural automorphism of the pullback functor. Restricting that automorphism
preserves its invertibility. Thus the supplied unit is invertible as well.
The assertion includes the empty open and requires no properness or coherence. -/
theorem tensorPullback_unit_restriction_isIso
    {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hp : IsIso (pullback.snd p U.ι))
    (adj : tensorPullback p ⊣ pushforward p) (A : Y.Modules) :
    IsIso ((restrictFunctor U.ι).map (adj.unit.app A))  := by
  have : IsIso (pullback.snd p U.ι) := hp
  let j := U.ι
  let g := pullback.fst p j
  let q := pullback.snd p j
  have hunit : IsIso ((restrictFunctor j).map (pullbackUnit p A)) := by
    apply Hom.isIso_iff_isIso_app.mpr
    intro W
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let V := j ''ᵁ W
    have hV : V ≤ j.opensRange := Scheme.Hom.image_le_opensRange j W
    have hg : p ⁻¹ᵁ V ≤ g.opensRange := by
      dsimp only [g]
      rw [Scheme.Hom.opensRange_pullbackFst]
      exact (TopologicalSpace.Opens.map p.base).monotone hV
    have hc : g ≫ p = q ≫ j := pullback.condition
    have hqj : IsOpenImmersion (g ≫ p) := by
      rw [hc]
      infer_instance
    have hcomp : Function.Bijective ((pullbackUnit (g ≫ p) A).app V) :=
      bijective_pullbackUnit_app_of_isOpenImmersion (g ≫ p) A (by
        simpa only [hc, Scheme.Hom.opensRange_comp_of_isIso] using hV)
    have hgunit : Function.Bijective
        ((pullbackUnit g ((pullback p).obj A)).app (p ⁻¹ᵁ V)) :=
      bijective_pullbackUnit_app_of_isOpenImmersion g _ hg
    have hiso := ConcreteCategory.bijective_of_isIso
      (((pullbackComp g p).inv.app A).app ((g ≫ p) ⁻¹ᵁ V))
    have hb : Function.Bijective
        (((pullbackUnit p A).app V) ≫
          ((pullbackUnit g ((pullback p).obj A)).app (p ⁻¹ᵁ V))) := by
      rw [← pullbackUnit_comp_app]
      exact hiso.comp hcomp
    exact (Function.Bijective.of_comp_iff' hgunit _).mp hb
  have he := (pullbackPushforwardAdjunction p).unit_leftAdjointUniq_hom_app adj A
  rw [← he, Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
