/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The gluing part of eventual smoothness.  A smooth finite-stage model `q` of the
pullback morphism, i.e. a smooth `q : Z ⟶ N.D.obj j.left` together with a comparison
isomorphism `e : Z ≅ pullback p (N.D.map j.hom)` over `N.D.obj j.left`, makes the pullback
morphism itself smooth at that stage, since smoothness is invariant under isomorphism.
Source: Stacks Project, Tag 0C0C, limits.tex, locality of smoothness after a common
cofiltered refinement.
(blueprint: lem-sbc-noetherian-approximation-smooth-stage-gluing) -/
theorem Scheme.NoetherianApproximation.smooth_stage_of_affine_models
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    (hmodel : ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (e : Z ≅ pullback p (N.D.map j.hom)),
        e.hom ≫ pullback.snd p (N.D.map j.hom) = q ∧ Smooth q) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom)) := by
  obtain ⟨j, Z, q, e, he, hq⟩ := hmodel
  refine ⟨j, ?_⟩
  have : pullback.snd p (N.D.map j.hom) = e.inv ≫ q := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [this]
  infer_instance

end AlgebraicGeometry
