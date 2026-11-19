import Langlands.ClassFieldTheory.Local.IntermediateUnitCorestriction
import Langlands.ClassFieldTheory.Local.UnitCohomologyTransport
import Mathlib.FieldTheory.SeparableDegree

/-! # Corestriction on actual separable-closure unit cohomology -/

noncomputable section

open CategoryTheory Langlands.Continuous

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

local notation "S" => SeparableClosure K
local notation "T" => SeparableClosure L

/-- Give the upper separable closure the lower base algebra from the tower. -/
abbrev separableClosureTowerAlgebra : Algebra K T :=
  ((algebraMap L T).comp (algebraMap K L)).toAlgebra

local instance (priority := low) lowerBaseOnUpperClosure : Algebra K T :=
  separableClosureTowerAlgebra K L

local instance (priority := low) lowerBaseOnUpperClosureTower : IsScalarTower K L T :=
  IsScalarTower.of_algebraMap_eq' rfl

variable [Algebra.IsSeparable K L]

/-- The same chosen lift as in separable-cohomology restriction is an
isomorphism for a separable extension of the base. -/
def separableClosureTowerEquiv : S ≃ₐ[K] T := by
  let : Algebra.IsSeparable K T := Algebra.IsSeparable.trans K L T
  let : IsSepClosure K T := ⟨inferInstance, inferInstance⟩
  exact AlgEquiv.ofBijective (IsSepClosed.lift : S →ₐ[K] T)
    (Normal.toIsAlgebraic.algHom_bijective₂ (IsSepClosed.lift : S →ₐ[K] T)
      (IsSepClosure.equiv K T S).toAlgHom).1

theorem separableClosureTowerEquiv_toAlgHom :
    (separableClosureTowerEquiv K L).toAlgHom = IsSepClosed.lift := rfl

/-- The canonical copy of the upper base pulled back to the lower closure. -/
def separableClosureBaseEmbedding : L →ₐ[K] S :=
  (separableClosureTowerEquiv K L).symm.toAlgHom.comp (IsScalarTower.toAlgHom K L T)

/-- The copy of the upper base in the common separable closure. -/
abbrev separableClosureBase : IntermediateField K S :=
  (separableClosureBaseEmbedding K L).fieldRange

local notation "E" => separableClosureBase K L

/-- The upper base identifies with its image in the common separable closure. -/
def separableClosureBaseEquiv : L ≃ₐ[K] E :=
  AlgEquiv.ofInjective (separableClosureBaseEmbedding K L)
    (separableClosureBaseEmbedding K L).injective

theorem separableClosureTowerEquiv_base (x : E) :
    separableClosureTowerEquiv K L (x : S) =
      algebraMap L T ((separableClosureBaseEquiv K L).symm x) := by
  let b := separableClosureBaseEquiv K L
  let e := separableClosureTowerEquiv K L
  have hb := congrArg (fun y : E => (y : S)) (b.apply_symm_apply x)
  change e.symm (algebraMap L T (b.symm x)) = (x : S) at hb
  exact (congrArg e hb).symm.trans (e.apply_symm_apply _)

/-- Compare upper continuous unit cohomology using the common field and
using the upper base's chosen separable closure. -/
def separableClosureUpperUnitIso (q : ℕ) :
    continuousCohomology q (discreteUnitsRepresentation E S) ≅
      continuousCohomology q (discreteUnitsRepresentation L T) :=
  unitCohomologyIsoOfRingEquiv (separableClosureBaseEquiv K L).symm.toRingEquiv
    (separableClosureTowerEquiv K L).toRingEquiv (separableClosureTowerEquiv_base K L) q

private abbrev forgetSeparableUnits :
    TopModuleCat.{u} IntegerScalars.{u} ⥤ ModuleCat.{u} IntegerScalars.{u} :=
  forget₂ _ _

variable [FiniteDimensional K L]

instance separableClosureBaseFinite : FiniteDimensional K E :=
  Module.Finite.equiv (separableClosureBaseEquiv K L).toLinearEquiv

/-- Actual corestriction from the upper separable closure's continuous unit
cohomology to that of the lower separable closure. -/
def separableUnitCorestriction (q : ℕ) :
    forgetSeparableUnits.obj (continuousCohomology q (discreteUnitsRepresentation L T)) ⟶
      forgetSeparableUnits.obj (continuousCohomology q (discreteUnitsRepresentation K S)) :=
  forgetSeparableUnits.map (separableClosureUpperUnitIso K L q).inv ≫
    intermediateUnitCorestriction K S E q

/-- Restrict to the actual open subgroup and move to the chosen upper closure. -/
def separableUnitRestrictionBySubgroup (q : ℕ) :
    continuousCohomology q (discreteUnitsRepresentation K S) ⟶
      continuousCohomology q (discreteUnitsRepresentation L T) :=
  intermediateUnitRestriction K S E q ≫ (separableClosureUpperUnitIso K L q).hom

/-- Corestriction following the open-subgroup restriction is the degree. -/
theorem separableUnitRestrictionBySubgroup_corestriction (q : ℕ) :
    forgetSeparableUnits.map (separableUnitRestrictionBySubgroup K L q) ≫
        separableUnitCorestriction K L q =
      Module.finrank K L • 𝟙 _ := by
  unfold separableUnitRestrictionBySubgroup separableUnitCorestriction
  rw [Functor.map_comp, Category.assoc, ← Category.assoc
    (forgetSeparableUnits.map (separableClosureUpperUnitIso K L q).hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    intermediateUnitRestriction_corestriction]
  rw [(separableClosureBaseEquiv K L).toLinearEquiv.finrank_eq]

end Langlands.ClassFieldTheory.Local
