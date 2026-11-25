/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.FlatScalarRealization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Flatness of scalar realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}
  [HasSheafify J AddCommGrpCat.{max u v}]
  (α : realizationRing J A ⟶ R)

private theorem scalarRestriction_exact :
    exactFunctor _ _ (restrictScalars.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)) := by
  let A' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J A)
  let R' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let res := restrictScalars.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)
  have : PreservesFiniteLimits (res ⋙ toSheaf A') :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{max u v} R'))
  have : PreservesFiniteColimits (res ⋙ toSheaf A') :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{max u v} R'))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves res (toSheaf A'),
    preservesFiniteColimits_of_reflects_of_preserves res (toSheaf A')⟩

private theorem scalarExtension_flat (M : realizationModules J A)
    (hM : IsFlatOnSite (J := J) (R := realizationRing J A) M) :
    IsFlatOnSite (J := J) (R := R) (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M) := by
  obtain ⟨e⟩ := nonempty_scalarTensorComparisonOfUniverses α M
  let A' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J A)
  let R' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let res := restrictScalars.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)
  let T := siteSheafTensorRight.{v, u, max u v, max u v} (A := realizationRing J A) M
  let S := siteSheafTensorRight.{v, u, max u v, max u v} (A := R)
    (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M)
  have : PreservesFiniteLimits res := (scalarRestriction_exact J α).1
  have : PreservesFiniteColimits res := (scalarRestriction_exact J α).2
  have : PreservesFiniteLimits T := hM.1
  have : PreservesFiniteColimits T := hM.2
  have : PreservesFiniteLimits (T ⋙ toSheaf A') := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (T ⋙ toSheaf A') := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (res ⋙ T ⋙ toSheaf A') := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (res ⋙ T ⋙ toSheaf A') := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (S ⋙ toSheaf R') := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits (S ⋙ toSheaf R') := preservesFiniteColimits_of_natIso e
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves S (toSheaf R'),
    preservesFiniteColimits_of_reflects_of_preserves S (toSheaf R')⟩

/-- Canonical scalar realization carries flat scalar modules to flat module sheaves.
Source: Stacks Project, Tags 03ET, 08FC and 05VD
(auxiliary; not a blueprint node).
Proof: the constant-module flatness theorem factors each finite scalar relation
locally, and so makes the constant module sheaf flat. Scalar extension preserves
this flatness: its tensor functor, after forgetting to abelian sheaves, is tensor
with the constant module after exact restriction of coefficients. The existing
sectionwise balanced tensor comparison supplies the natural isomorphism. The
forgetful functor reflects exactness. No flatness of the target algebra itself
is required; zero modules, the zero ring and empty sites are included. -/
theorem flatScalarRealization_flat (M : ModuleCat.{max u v} A) (hM : Module.Flat A M) :
    IsFlatOnSite (J := J) (R := R) ((flatScalarRealization J α).obj M) := by
  exact scalarExtension_flat J α _ (isFlatOnSite_constantModule J A M hM)

end SheafOfModules
