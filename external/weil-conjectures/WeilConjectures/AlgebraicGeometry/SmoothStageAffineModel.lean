/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The affine-chart part of eventual smoothness: after passing to a later stage `j`,
the base change `pullback.snd p (N.D.map j.hom)` of `p` is smooth.  This is the affine
descent argument of Tags 0CAQ and 01ZM(2)-(3) on a finite affine cover of `Y`.
Source: Stacks Project, Tag 0C0C, limits.tex, affine reduction of lemma-descend-smooth.
(blueprint: lem-sbc-noetherian-approximation-smooth-stage-affine-model) -/
theorem Scheme.NoetherianApproximation.exists_smooth_affine_model
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y X : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i)) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom)) :=
  Scheme.exists_smooth_stage_of_affine_limit N.D N.π N.isLimit N.isAffineHom_map
    N.isNoetherian_obj (fun _ ↦ inferInstance) p f a H

end AlgebraicGeometry
