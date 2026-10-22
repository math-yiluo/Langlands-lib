import Langlands.Sheaf.Equivariant.Site
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# The abelian category of equivariant module sheaves

Mathlib sheafifies module-valued presheaves on the transport site, so its
sheaves form a Grothendieck abelian category. The equivalence with the
published equivariant sheaf category transports this structure.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] (X : Type u) [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- Equivariant module sheaves form an abelian category. Cokernels are
sheafified presheaf cokernels for the transport topology. -/
instance topologicalSheaf_abelian : Abelian (TopologicalSheaf G X (ModuleCat.{u} R)) :=
  haveI : HasFiniteProducts (TopologicalSheaf G X (ModuleCat.{u} R)) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
      (sheafEquivalence G X (ModuleCat.{u} R)).functor⟩
  abelianOfEquivalence (sheafEquivalence G X (ModuleCat.{u} R)).functor

/-- Equivariant module sheaves form a Grothendieck abelian category. -/
instance topologicalSheaf_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u} (TopologicalSheaf G X (ModuleCat.{u} R)) :=
  IsGrothendieckAbelian.of_equivalence (sheafEquivalence G X (ModuleCat.{u} R)).symm

/-- Equivariant module sheaves have enough injectives. -/
instance topologicalSheaf_enoughInjectives :
    EnoughInjectives (TopologicalSheaf G X (ModuleCat.{u} R)) :=
  inferInstance

end Langlands.Sheaf.Equivariant
