/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover

/-! # Projection formula locality: local to global

If the projection-formula map is an isomorphism after restriction to every member of an open
cover, it is an isomorphism (Stacks Project, Lemma 36.22.1, Tag 08EU). -/

@[expose] public section
universe u w v
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
set_option autoImplicit false
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
/-- Local isomorphisms of the projection map imply its global isomorphism.
Source: Stacks Project, perfect.tex, Lemma 36.22.1 (Tag 08EU).
(blueprint: lem-pc-projection-locality-local-to-global)
The proof identifies restrictions with maps for restricted morphisms and uses
cohomology sheaf locality on an open cover. -/
theorem projectionFormula_local_to_global
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (K : schemeDerivedCategory Y)
    (I : Type v) (U : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ U i)
    (φ : ((schemeDerivedDirectImage f).obj E) ⊗ K ⟶
      (schemeDerivedDirectImage f).obj (E ⊗ ((derivedPullback f).obj K))) :
    (∀ i : I, IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ)) →
      IsIso φ := by
  intro hlocal
  apply (DerivedCategory.isIso_iff _ φ).mpr
  intro n
  have hU : ⨆ i, U i = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  apply (sheaf_module_isIso_iff_isIso_over_open_cover.{u, u, v}
    Y.toRingedSpace I U hU _ _
    ((DerivedCategory.homologyFunctor _ n).map φ)).mpr
  intro i
  have := hlocal i
  have hhom : IsIso
      ((schemeOpenRestriction Y (U i)).map
        ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction Y (U i)).mapDerivedCategoryHomologyFunctorIso n) φ).mpr
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ))
        exact Functor.map_isIso _ _)
  let G := (Scheme.Modules.overEquiv (U i)).functor
  have : IsIso (G.map (((DerivedCategory.homologyFunctor _ n).map φ).over (U i))) :=
    hhom
  exact isIso_of_reflects_iso _ G
end AlgebraicGeometry
