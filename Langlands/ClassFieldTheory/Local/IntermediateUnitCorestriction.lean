import Langlands.ClassFieldTheory.Local.SeparableInertiaH2
import Langlands.Cohomology.Continuous.CorestrictionIndexProof

/-! # Continuous unit corestriction on a common Galois field -/

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω)

private def fixingSubgroupUnitsIso :
    TopRep.res (fixingSubgroupContinuousEquiv E : Gal(Ω/E) →ₜ* E.fixingSubgroup)
      (TopRep.res E.fixingSubgroup.subtype (discreteUnitsRepresentation K Ω)) ≅
        discreteUnitsRepresentation E Ω where
  hom.hom' :=
    { toContinuousLinearMap := { toLinearMap := LinearMap.id, cont := continuous_id }
      isIntertwining' _ := rfl }
  inv.hom' :=
    { toContinuousLinearMap := { toLinearMap := LinearMap.id, cont := continuous_id }
      isIntertwining' _ := rfl }
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- Continuous cohomology over the actual fixing subgroup is continuous
unit cohomology over its intermediate field. -/
def intermediateUnitCohomologyIso (q : ℕ) :
    continuousCohomology q
      ((galoisUnitDiscreteModule K Ω).restrict E.fixingSubgroup).toTopRep ≅
        continuousCohomology q (discreteUnitsRepresentation E Ω) :=
  continuousCohomologyIso (fixingSubgroupContinuousEquiv E) (fixingSubgroupUnitsIso K Ω E) q

/-- Restriction of actual continuous unit cohomology to an intermediate field. -/
def intermediateUnitRestriction (q : ℕ) :
    continuousCohomology q (discreteUnitsRepresentation K Ω) ⟶
      continuousCohomology q (discreteUnitsRepresentation E Ω) :=
  continuousRestriction (galoisUnitDiscreteModule K Ω) E.fixingSubgroup q ≫
    (intermediateUnitCohomologyIso K Ω E q).hom

variable [FiniteDimensional K E]

/-- The actual fixing subgroup of a finite intermediate field is open. -/
abbrev intermediateFieldFixingOpenSubgroup : OpenSubgroup Gal(Ω/K) :=
  ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

local notation "H" => intermediateFieldFixingOpenSubgroup K Ω E
local notation "A" => galoisUnitDiscreteModule K Ω
private abbrev forgetUnits :
    TopModuleCat.{u} IntegerScalars.{u} ⥤ ModuleCat.{u} IntegerScalars.{u} :=
  forget₂ _ _

local instance intermediateUnitFixingGroupTopological : IsTopologicalGroup (H) := by
  change IsTopologicalGroup E.fixingSubgroup
  infer_instance

/-- Corestriction on continuous cohomology of actual units in the common
Galois field, transported from its open fixing subgroup. -/
def intermediateUnitCorestriction (q : ℕ) :
    forgetUnits.obj (continuousCohomology q (discreteUnitsRepresentation E Ω)) ⟶
      forgetUnits.obj (continuousCohomology q (discreteUnitsRepresentation K Ω)) :=
  forgetUnits.map (intermediateUnitCohomologyIso K Ω E q).inv ≫
    continuousCorestriction A H q

set_option backward.isDefEq.respectTransparency false in
theorem intermediateUnitCohomologyIso_comp_corestriction (q : ℕ) :
    forgetUnits.map (intermediateUnitCohomologyIso K Ω E q).hom ≫
        intermediateUnitCorestriction K Ω E q =
      continuousCorestriction A H q := by
  unfold intermediateUnitCorestriction
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Corestriction following restriction is multiplication by the actual
degree of the finite intermediate field. -/
theorem intermediateUnitRestriction_corestriction (q : ℕ) :
    forgetUnits.map (intermediateUnitRestriction K Ω E q) ≫
      intermediateUnitCorestriction K Ω E q =
    Module.finrank K E • 𝟙 (forgetUnits.obj
      (continuousCohomology q (discreteUnitsRepresentation K Ω))) := by
  unfold intermediateUnitRestriction
  rw [Functor.map_comp, Category.assoc, intermediateUnitCohomologyIso_comp_corestriction]
  have h := continuousRestriction_corestriction_index A H q
  exact h.trans (congrArg (fun d : ℕ => d • 𝟙 _)
    (IntermediateField.finrank_eq_fixingSubgroup_index Ω E).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Finite normal stages inside the fixing subgroup compute this
continuous corestriction. -/
theorem finiteStageToContinuous_comp_intermediateUnitCorestriction
    (N : OpenNormalSubgroup Gal(Ω/K)) (hNE : N.toSubgroup ≤ E.fixingSubgroup) (q : ℕ) :
    finiteStageToContinuous ((A).restrict (H).toSubgroup) (restrictOpenNormal H N) q ≫
      forgetUnits.map (intermediateUnitCohomologyIso K Ω E q).hom ≫
      intermediateUnitCorestriction K Ω E q =
    finiteCorestriction (A).toRep H N hNE q ≫ finiteStageToContinuous A N q := by
  rw [intermediateUnitCohomologyIso_comp_corestriction]
  exact finiteStageToContinuous_comp_corestriction A H N hNE q

end Langlands.ClassFieldTheory.Local
