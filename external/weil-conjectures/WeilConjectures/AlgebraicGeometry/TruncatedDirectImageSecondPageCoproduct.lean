/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSecondPageCoproductMono
import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSecondPageCoproductEpi

/-! # The second-page coproduct comparison for lower-truncated direct image

Source: Stacks Project, Tag 08DZ, the reduction using the spectral sequences of Tag 015J
(blueprint: lem-pc-truncated-direct-image-second-page-coproduct).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The second-page maps for a uniformly lower-truncated ambient coproduct are isomorphisms.
Source: Stacks Project, Tag 08DZ, bounded-below spectral-sequence paragraph, and Tag 015J
(blueprint: lem-pc-truncated-direct-image-second-page-coproduct).

Proof: Choose representatives of the summands and their termwise coproduct. The theorem
`derivedAmbientDirectSums` identifies the given ambient cofan with this coproduct and
identifies its cohomology maps with the canonical coprojections. Exactness of sums implies
that lower truncation commutes with sums: in degree r >= a its cohomology is the original
cohomology, naturally in every coprojection; in degree r < a all these sheaves are zero.
Thus the cohomology cofan of the lower truncations is a coproduct. Each cohomology sheaf
is quasi-coherent, including its coproduct by `Scheme.Modules.isQuasicoherent_sigma`.
For an affine open V of Y, the inverse image is quasi-compact and quasi-separated. Apply
`Scheme.moduleCohomology_directSum_bijective` there to the restricted cohomology cofan.
The higher-direct-image presheaf theorem identifies R^p f_* with the sheafification of
these cohomology presheaves, naturally in the coefficient sheaf and in restriction to
smaller opens. Module sheafification preserves coproducts. On the affine basis the
resulting comparison is therefore an isomorphism, so it is an isomorphism of sheaves.
The natural comparison between the unbounded derived functor on a degree-zero object
and the ordinary right derived functor identifies this map with the displayed map.
Empty families give zero coproducts; degrees below a are covered by the zero cofan. -/
theorem truncated_directImage_secondPage_coproduct
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a : ℤ) (p : ℕ) (r : ℤ) :
    IsIso (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) := by
  have hm : Mono (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) :=
    truncated_directImage_secondPage_coproduct_mono f I E S ι hc a p r
  have he : Epi (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) :=
    truncated_directImage_secondPage_coproduct_epi f I E S ι hc a p r
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry
