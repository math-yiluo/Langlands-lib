import Langlands.Representation.Category.RenardFinitenessProof
import Langlands.CategoryTheory.RenardModuleNoetherianProof

/-!
# Subobject unions and Noetherianity for smooth representations

These are unconditional comparisons for the existing smooth category and its
actual group-algebra action. They do not assert that every finite-type smooth
representation of an arbitrary topological group is Noetherian.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G] [TopologicalSpace G]

/-- The union in the actual smooth subobject order, constructed by taking the
supremum of the corresponding group-algebra submodules. -/
def subobjectUnion (A : SmoothRep.{uR, uG, uV} R G)
    (S : Set (Subobject A)) : Subobject A :=
  (groupAlgebraSubobjectOrderIso A).symm
    (sSup ((groupAlgebraSubobjectOrderIso A) '' S))

/-- The chosen union is a least upper bound, including for the empty set. -/
theorem subobjectUnion_isLUB (A : SmoothRep.{uR, uG, uV} R G)
    (S : Set (Subobject A)) : IsLUB S (subobjectUnion A S) :=
  (groupAlgebraSubobjectOrderIso A).isLUB_image.mp (isLUB_sSup _)

/-- The chosen union corresponds to the supremum of the actual submodules. -/
theorem groupAlgebraSubobjectOrderIso_subobjectUnion
    (A : SmoothRep.{uR, uG, uV} R G) (S : Set (Subobject A)) :
    groupAlgebraSubobjectOrderIso A (subobjectUnion A S) =
      sSup ((groupAlgebraSubobjectOrderIso A) '' S) :=
  (groupAlgebraSubobjectOrderIso A).apply_symm_apply _

/-- Every smooth representation admits all of Renard's subobject unions. -/
theorem hasSubobjectUnions (A : SmoothRep.{uR, uG, uV} R G) :
    Langlands.Renard.HasSubobjectUnions A :=
  fun S => ⟨subobjectUnion A S, subobjectUnion_isLUB A S⟩

/-- The smooth category admits arbitrary subobject unions without any
Noetherianity or local-field assumption. -/
theorem hasAllSubobjectUnions :
    Langlands.Renard.HasAllSubobjectUnions (SmoothRep.{uR, uG, uV} R G) :=
  hasSubobjectUnions

private theorem noetherian_of_subobjectOrderIso
    {C D : Type*} [Category C] [Category D] {X : C} {Y : D}
    (e : Subobject X ≃o Subobject Y)
    (hY : Langlands.Renard.IsNoetherianObject Y) :
    Langlands.Renard.IsNoetherianObject X := by
  intro S hS
  obtain ⟨Q, ⟨P, hP, rfl⟩, hmax⟩ := hY (e '' S) (hS.image e)
  refine ⟨P, hP, ?_⟩
  intro Q hQ hPQ
  exact e.injective (hmax (e Q) ⟨Q, hQ, rfl⟩ (e.monotone hPQ))

/-- Renard's maximal-subobject definition of a Noetherian smooth object is
exactly Noetherianity for its existing group-algebra module. -/
theorem renardNoetherian_iff (A : SmoothRep.{uR, uG, uV} R G) :
    Langlands.Renard.IsNoetherianObject A ↔
      IsNoetherian R[G] A.representation.asModule := by
  let e := moduleSubobjectOrderIso A
  exact (show Langlands.Renard.IsNoetherianObject A ↔
      Langlands.Renard.IsNoetherianObject
        (ModuleCat.of R[G] A.representation.asModule) from
    ⟨noetherian_of_subobjectOrderIso e.symm,
      noetherian_of_subobjectOrderIso e⟩).trans
        (Langlands.Renard.ModuleNoetherian.object_iff _ _)

end Langlands.SmoothRep
