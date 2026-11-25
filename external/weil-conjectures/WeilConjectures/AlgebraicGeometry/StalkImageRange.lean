/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Images

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Stalk exactness identifies the range of the stalk image inclusion with the
range of the stalk map. This is the image part of the proof of
`ideal_multiplication_stalk_range`.
Source: Stacks Project, Modules, Lemma 01AG.
(blueprint: lem-weil-pbc-ideal-multiplication-stalk-range-image).
-/
theorem stalk_image_inclusion_range {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (image.ι f)).hom = LinearMap.range (S.map f).hom := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hr := ((RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.2.1 x).2.2
  have he : S.map (Abelian.imageIsoImage f).hom ≫ S.map (image.ι f) =
      S.map (Abelian.image.ι f) := by
    rw [← S.map_comp, Abelian.imageIsoImage_hom_comp_image_ι]
  have hs : Function.Surjective (S.map (Abelian.imageIsoImage f).hom).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  calc
    LinearMap.range (S.map (image.ι f)).hom =
        LinearMap.range (S.map (Abelian.image.ι f)).hom := by
      rw [← he, ModuleCat.hom_comp,
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]
    _ = LinearMap.range (S.map f).hom := hr

end
end AlgebraicGeometry.Scheme
