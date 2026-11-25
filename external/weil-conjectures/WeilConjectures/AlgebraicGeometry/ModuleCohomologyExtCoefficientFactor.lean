/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! # Ext coefficient factorization

Source: Stacks Project, Tag 01F7.
(blueprint: new-module-cohomology-ext-coefficient-factor)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Ext coefficient factorization.

Source: Stacks Project, Tag 01F7.
(blueprint: new-module-cohomology-ext-coefficient-factor)

Proof: Apply sheafComparison_naturality to the coefficient square from coeff_naturality, with
the target module map equal to its identity. Functoriality sends that identity to an identity,
and H.map_id_apply removes it. -/
theorem moduleCohomology_ext_coefficient_factor
    {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules} {F : X.Modules}
    (φ : N ⟶ (pushforward f).obj F) (p : ℕ)
    (x : Sheaf.H (C := TopologicalSpace.Opens Y) (J := Opens.grothendieckTopology Y)
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) p) :
    Sheaf.H.map (C := TopologicalSpace.Opens X)
      (J := Opens.grothendieckTopology X)
      (coeff (X := X) (Y := Y) (M := (pushforward f).obj F) (N := F)
      f (𝟙 ((pushforward f).obj F))) p
      (Sheaf.H.mapFunctor (C := TopologicalSpace.Opens Y)
        (D := TopologicalSpace.Opens X) (J := Opens.grothendieckTopology Y)
        (K := Opens.grothendieckTopology X) (invImage f) (constIso f).symm
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p
        (Sheaf.H.map (C := TopologicalSpace.Opens Y)
          (J := Opens.grothendieckTopology Y)
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) p x)) =
    Sheaf.H.map (C := TopologicalSpace.Opens X)
      (J := Opens.grothendieckTopology X) (coeff (X := X) (Y := Y) (M := N) (N := F) f φ) p
      (Sheaf.H.mapFunctor (C := TopologicalSpace.Opens Y)
        (D := TopologicalSpace.Opens X) (J := Opens.grothendieckTopology Y)
        (K := Opens.grothendieckTopology X) (invImage f) (constIso f).symm
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) p x) := by
  have hc := coeff_naturality (X := X) (Y := Y)
    (M := N) (M' := (pushforward f).obj F) (N := F) (N' := F)
    f φ (𝟙 ((pushforward f).obj F)) φ (𝟙 F) (by simp)
  have hn := sheafComparison_naturality
    (C := Opens Y) (D := Opens X)
    (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
    (F := (SheafOfModules.toSheaf Y.ringCatSheaf).obj N)
    (E := (SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F))
    (F' := (SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    (E' := (SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    (invImage f) (constIso f).symm
    (coeff (X := X) (Y := Y) (M := N) (N := F) f φ)
    (coeff (X := X) (Y := Y) (M := (pushforward f).obj F) (N := F)
      f (𝟙 ((pushforward f).obj F)))
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (𝟙 F)) hc p x
  set_option backward.isDefEq.respectTransparency false in
    simpa only [CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply] using hn


end AlgebraicGeometry.Scheme.Modules
