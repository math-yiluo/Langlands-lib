import Langlands.ClassFieldTheory.Local.RelativeBaseFieldTransport
import Langlands.ClassFieldTheory.Local.RelativeContinuousCorestriction
import Langlands.ClassFieldTheory.Local.SeparableClosureCorestriction

/-! # Finite stages of corestriction on separable-closure units -/

noncomputable section

open CategoryTheory Langlands.Continuous

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

local notation "S" => SeparableClosure K
local notation "T" => SeparableClosure L
local notation "E" => separableClosureBase K L

variable (N : OpenNormalSubgroup Gal(SeparableClosure K/K))

/-- The finite Galois fixed field of the ambient open normal subgroup. -/
abbrev separableClosureStageField (P : OpenNormalSubgroup Gal(S/K)) : IntermediateField K S :=
  @IntermediateField.fixedField K _ S _ _ P.toSubgroup

local notation "NC" => FixedFieldRefinement.closed K S N
set_option quotPrecheck false in
local notation "M" => ↥(separableClosureStageField K N)

variable (hNE : N.toSubgroup ≤ (separableClosureBase K L).fixingSubgroup)

/-- The upper base embeds in an ambient finite stage by way of its copy in
the lower separable closure. -/
def separableClosureStageBaseEmbedding : L →ₐ[K] M :=
  (IntermediateField.inclusion (le_fixedField_of_le_fixingSubgroup K S E (NC) hNE)).comp
    (separableClosureBaseEquiv K L).toAlgHom

/-- Use the preceding embedding for the upper base algebra of the finite stage. -/
abbrev separableClosureStageAlgebra : Algebra L M :=
  (separableClosureStageBaseEmbedding K L N hNE).toRingHom.toAlgebra

theorem separableClosureStageAlgebra_apply (x : L) :
    letI := separableClosureStageAlgebra K L N hNE
    letI := fixedFieldRestrictedAlgebra K S E (NC) hNE
    algebraMap L M x = algebraMap E M (separableClosureBaseEquiv K L x) := rfl

theorem separableClosureStageTowerBase :
    letI := separableClosureStageAlgebra K L N hNE
    IsScalarTower K L M :=
  IsScalarTower.of_algHom (separableClosureStageBaseEmbedding K L N hNE)

/-- Embed the same finite Galois stage into the upper separable closure. -/
def separableClosureStageEmbedding : M →ₐ[K] T :=
  (separableClosureTowerEquiv K L).toAlgHom.comp
    (separableClosureStageField K N).val

/-- This is the actual algebra structure from the finite stage embedding. -/
abbrev separableClosureStageTopAlgebra : Algebra M T :=
  (separableClosureStageEmbedding K L N).toRingHom.toAlgebra

theorem separableClosureStageTowerTop :
    letI := separableClosureStageAlgebra K L N hNE
    letI := separableClosureStageTopAlgebra K L N
    IsScalarTower L M T := by
  let := separableClosureStageAlgebra K L N hNE
  let := separableClosureStageTopAlgebra K L N
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap L T x =
    separableClosureTowerEquiv K L (((separableClosureBaseEquiv K L) x : E) : S)
  rw [separableClosureTowerEquiv_base, AlgEquiv.symm_apply_apply]

private abbrev forgetStageUnits :
    TopModuleCat.{u} IntegerScalars.{u} ⥤ ModuleCat.{u} IntegerScalars.{u} :=
  forget₂ _ _

variable [FiniteDimensional K L]

/-- The actual relative unit cohomology of the upper base maps into the
continuous unit cohomology of its chosen separable closure. -/
def separableClosureStageUnitInflation (q : ℕ) :
    letI := separableClosureStageAlgebra K L N hNE
    relativeCohomology L M q ⟶
      forgetStageUnits.obj (continuousCohomology q (discreteUnitsRepresentation L T)) := by
  let := separableClosureStageAlgebra K L N hNE
  let := fixedFieldRestrictedAlgebra K S E (NC) hNE
  let b := separableClosureBaseEquiv K L
  exact (relativeBaseFieldCohomologyIso b (separableClosureStageAlgebra_apply K L N hNE) q).hom ≫
    intermediateFixedFieldUnitInflation K S E N hNE q ≫
    forgetStageUnits.map (separableClosureUpperUnitIso K L q).hom

/-- Absolute corestriction on the upper finite-stage inflation is relative
corestriction followed by lower finite-stage inflation. -/
theorem separableClosureStageUnitInflation_corestriction (q : ℕ) [NeZero q] :
    letI := separableClosureStageAlgebra K L N hNE
    letI := separableClosureStageTowerBase K L N hNE
    letI := fixedField_openNormal_finiteDimensional K S N
    separableClosureStageUnitInflation K L N hNE q ≫ separableUnitCorestriction K L q =
      ModuleCat.ofHom (relativeCorestriction K L M q) ≫ fixedFieldUnitInflation K S N q := by
  let := separableClosureStageAlgebra K L N hNE
  let := separableClosureStageTowerBase K L N hNE
  let := fixedField_openNormal_finiteDimensional K S N
  let := fixedFieldRestrictedAlgebra K S E (NC) hNE
  let := fixedFieldRestrictedTowerBase K S E (NC) hNE
  let b := separableClosureBaseEquiv K L
  let e := separableClosureUpperUnitIso K L q
  let hb := separableClosureStageAlgebra_apply K L N hNE
  let f := (relativeBaseFieldCohomologyIso b hb q).hom
  change (f ≫ intermediateFixedFieldUnitInflation K S E N hNE q ≫
      forgetStageUnits.map e.hom) ≫
      (forgetStageUnits.map e.inv ≫ intermediateUnitCorestriction K S E q) = _
  simp only [Category.assoc]
  rw [← Category.assoc (forgetStageUnits.map e.hom), ← Functor.map_comp,
    e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    intermediateFixedFieldUnitInflation_corestriction, ← Category.assoc f]
  exact congrArg (fun t => t ≫ fixedFieldUnitInflation K S N q)
    (relativeBaseFieldCohomologyIso_corestriction b hb q)

/-- Such finite stages suffice to represent every upper continuous class. -/
theorem exists_separableClosureStageUnitInflation (q : ℕ)
    (x : continuousCohomology q (discreteUnitsRepresentation L T)) :
    ∃ (P : OpenNormalSubgroup Gal(S/K)) (hPE : P.toSubgroup ≤ (E).fixingSubgroup),
      letI := separableClosureStageAlgebra K L P hPE
      ∃ y : relativeCohomology L (separableClosureStageField K P) q,
        separableClosureStageUnitInflation K L P hPE q y = x := by
  let e := separableClosureUpperUnitIso K L q
  obtain ⟨P, hPE, y, hy⟩ := exists_intermediateFixedFieldUnitInflation K S E q (e.inv x)
  let := separableClosureStageAlgebra K L P hPE
  let := fixedFieldRestrictedAlgebra K S E (FixedFieldRefinement.closed K S P) hPE
  let f := relativeBaseFieldCohomologyIso (separableClosureBaseEquiv K L)
    (separableClosureStageAlgebra_apply K L P hPE) q
  refine ⟨P, hPE, f.inv y, ?_⟩
  change e.hom (intermediateFixedFieldUnitInflation K S E P hPE q (f.hom (f.inv y))) = x
  rw [Iso.inv_hom_id_apply, hy, Iso.inv_hom_id_apply]

end Langlands.ClassFieldTheory.Local
