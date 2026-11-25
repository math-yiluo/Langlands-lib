/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.Curve.ModuleSheafUnderlyingPreservesColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Colimits under the constant-coefficient module forgetful functor -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


/-- Forgetting constant-ring module structures preserves a module-sheaf colimit cocone.
Source: Stacks Project, Tags 03CO and 03CY.
(blueprint: lem-pbc-u2-module-sheaf-underlying-colimit)

Proof: Form the colimit of the underlying module presheaves sectionwise. The forgetful
functor from modules to abelian groups preserves these colimits: each compatible family
of additive maps extends uniquely, and its extension commutes with scalar multiplication
when the family is linear. Sheafify this presheaf colimit. Module sheafification and
abelian sheafification have identical underlying abelian sheaves, since their local
relations and gluing are the same. Therefore the sheafified underlying abelian cocone
has the colimit universal property. Any other module colimit cocone is uniquely
isomorphic to this one compatibly with every leg. Forget this isomorphism to transfer
the abelian colimit property to the given cocone. This works for empty diagrams as
well as filtered diagrams, and for the zero ring and the zero sheaf. -/
theorem moduleSheaf_underlying_isColimit
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {A : Type (u + 1)} [SmallCategory A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {c : Cocone D} (hc : IsColimit c) :
    Nonempty (IsColimit ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapCocone c)) := by
  let _ := moduleSheaf_underlying_preserves_colimit (X := X) (Λ := Λ) (D := D)
  exact PreservesColimit.preserves hc

end AlgebraicGeometry.Scheme
