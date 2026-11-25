/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import all WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The module direct image along a closed immersion preserves homology of short complexes.
Source: Stacks Tags 00AE and 01AX.
(blueprint: lem-sc-closed-immersion-algebra-direct-image-preserves-homology)
-/
theorem closedImmersion_algebraDirectImage_preservesHomology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).PreservesHomology := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)
  let R := moduleRings Z.toRingedSpace
  let S := moduleRings (directImageAlgebraSpace i)
  have hE : F.PreservesEpimorphisms := by
    constructor
    intro M N g hg
    have : Epi ((SheafOfModules.toSheaf R).map g) := Functor.map_epi _ _
    have hpush := TopCat.epi_pushforward_closedEmbedding i.base i.isClosedEmbedding
      ((SheafOfModules.toSheaf R).map g)
    have : Epi ((SheafOfModules.toSheaf S).map (F.map g)) := hpush
    exact Functor.epi_of_epi_map (SheafOfModules.toSheaf S) inferInstance
  let := hE
  have : PreservesFiniteLimits F := by
    dsimp [F, RingedSpace.moduleDirectImage]
    infer_instance
  exact Functor.preservesHomology_of_preservesEpis_and_kernels F

end AlgebraicGeometry

