/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/--
The sheaf-level forgetful functor from constant-ring module sheaves to abelian
sheaves preserves colimits of any fixed diagram.  This is the bridge needed to
transport a module-sheaf colimit cocone to the underlying abelian sheaves.
Source: Stacks Project, Tags 03CO and 03CY.
(blueprint: theorem-cohomology-curves--7)

Proof: The module forgetful functor preserves colimits and the limits used in
matching families, so Mathlib's plus-construction comparison shows that it
commutes with sheafification. The resulting natural isomorphism identifies
module sheafification followed by forgetting with presheaf forgetting followed
by abelian sheafification. Both functors on the latter side preserve colimits.
The sheafification adjunction has fully faithful right adjoint, so preservation
after precomposition with sheafification implies preservation on sheaves.
-/
theorem moduleSheaf_underlying_preserves_colimit
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {A : Type (u + 1)} [SmallCategory A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} :
    PreservesColimit D (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  let J := X.smallEtaleTopology
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : J.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification J U
  have : PreservesColimitsOfShape A (sheafCompose J U) := by
    rw [(sheafificationAdjunction J (ModuleCat.{u + 1} Λ)).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J U
        (sheafificationAdjunction J (ModuleCat.{u + 1} Λ))
        (sheafificationAdjunction J AddCommGrpCat.{u + 1}))
  infer_instance

end AlgebraicGeometry.Scheme
