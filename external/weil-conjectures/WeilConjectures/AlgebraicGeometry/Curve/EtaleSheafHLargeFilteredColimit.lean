/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-! # Continuity of Ext cohomology for large filtered diagrams -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Large-universe filtered-colimit continuity for the derived etale cohomology functor.
Source: Stacks Project, Tags 03Q5 and 0739; the same finite-cover and injective-resolution
argument as the small-index theorem, with the index category in `Type (u + 1)`.
(blueprint: lem-pbc-u2-sheafH-large-filtered-colimit-derived)

The proof repeats the filtered-colimit continuity argument while tracking the larger
indexing universe. This intermediate result is isolated so the Ext comparison can be
transported separately. -/
theorem etaleCohomology_isColimit_large_filtered
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).mapCocone c)) := by
  obtain ⟨B, horder, hdirected, hnonempty, F, hfinal⟩ := IsFiltered.exists_directed A
  let := horder
  let := hdirected
  let := hnonempty
  let := hfinal
  have hF : IsColimit (c.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c).symm hc
  obtain ⟨hH⟩ := etaleCohomology_isColimit_of_isDirected X hF q
  exact ⟨Functor.Final.isColimitWhiskerEquiv F _ hH⟩

/-- (blueprint: lem-pbc-u2-sheafH-large-filtered-colimit) -/
theorem sheafH_isColimit_large_filtered
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit ((Sheaf.functorH X.smallEtaleTopology q).mapCocone c)) := by
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso X q
  exact ⟨IsColimit.mapCoconeEquiv e.symm
    (etaleCohomology_isColimit_large_filtered X hc q).some⟩

end AlgebraicGeometry.Scheme
