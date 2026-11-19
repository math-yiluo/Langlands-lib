import Langlands.ClassFieldTheory.Local.FixedFieldRelativeCorestriction

/-! # Relative cohomology computes continuous corestriction -/

noncomputable section

open CategoryTheory Langlands.Continuous

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E]

private abbrev forgetUnitTopology :
    TopModuleCat.{u} IntegerScalars.{u} ⥤ ModuleCat.{u} IntegerScalars.{u} :=
  forget₂ _ _

local notation "A" => galoisUnitDiscreteModule K Ω
local notation "H" => intermediateFieldFixingOpenSubgroup K Ω E

variable (N : OpenNormalSubgroup Gal(Ω/K)) (hNE : N.toSubgroup ≤ E.fixingSubgroup)

local notation "NC" => FixedFieldRefinement.closed K Ω N
local notation "M" => IntermediateField.fixedField N.toSubgroup

/-- Inflate relative classes from the actual finite fixed field over the
intermediate base via the finite quotient of its Krull fixing subgroup. -/
def intermediateFixedFieldUnitInflation (q : ℕ) :
    letI := fixedFieldRestrictedAlgebra K Ω E (NC) hNE
    relativeCohomology E M q ⟶
      forgetUnitTopology.obj (continuousCohomology q (discreteUnitsRepresentation E Ω)) := by
  let := fixedFieldRestrictedAlgebra K Ω E (NC) hNE
  let := fixedFieldRestrictedTowerBase K Ω E (NC) hNE
  let := fixedFieldRestrictedTowerTop K Ω E (NC) hNE
  exact (fixedFieldRestrictedCohomologyIso K Ω E (NC) hNE q).inv ≫
    finiteStageToContinuous ((A).restrict E.fixingSubgroup) (restrictOpenNormal H N) q ≫
    forgetUnitTopology.map (intermediateUnitCohomologyIso K Ω E q).hom

/-- Continuous corestriction computes relative corestriction followed by
finite-stage inflation. -/
theorem intermediateFixedFieldUnitInflation_corestriction (q : ℕ) [NeZero q] :
    letI := fixedFieldRestrictedAlgebra K Ω E (NC) hNE
    letI := fixedFieldRestrictedTowerBase K Ω E (NC) hNE
    letI := fixedField_openNormal_finiteDimensional K Ω N
    intermediateFixedFieldUnitInflation K Ω E N hNE q ≫
        intermediateUnitCorestriction K Ω E q =
      ModuleCat.ofHom (relativeCorestriction K E M q) ≫ fixedFieldUnitInflation K Ω N q := by
  let := fixedFieldRestrictedAlgebra K Ω E (NC) hNE
  let := fixedFieldRestrictedTowerBase K Ω E (NC) hNE
  let := fixedFieldRestrictedTowerTop K Ω E (NC) hNE
  let := fixedField_openNormal_finiteDimensional K Ω N
  let eE := fixedFieldRestrictedCohomologyIso K Ω E (NC) hNE q
  let eK := fixedFieldCohomologyIso K Ω (NC) q
  let tr := finiteCorestriction (A).toRep H N hNE q
  let ix := finiteStageToContinuous A N q
  have hstage := finiteStageToContinuous_comp_intermediateUnitCorestriction K Ω E N hNE q
  have hfield := finiteCorestriction_fixedFieldCohomologyIso K Ω E N hNE q
  apply (cancel_epi eE.hom).mp
  change eE.hom ≫ (eE.inv ≫ _ ≫ _) ≫ intermediateUnitCorestriction K Ω E q =
    eE.hom ≫ ModuleCat.ofHom (relativeCorestriction K E M q) ≫ eK.inv ≫ ix
  simp only [Category.assoc, eE.hom_inv_id_assoc, hstage]
  calc
    tr ≫ ix = (tr ≫ eK.hom) ≫ eK.inv ≫ ix := by
      simp only [Category.assoc, eK.hom_inv_id_assoc]
    _ = eE.hom ≫ ModuleCat.ofHom (relativeCorestriction K E M q) ≫ eK.inv ≫ ix := by
      change (tr ≫ (fixedFieldCohomologyIso K Ω (NC) q).hom) ≫ _ = _
      rw [hfield, Category.assoc]

/-- Every class over the intermediate base comes from a fixed field finite
Galois over the lower base. -/
theorem exists_intermediateFixedFieldUnitInflation (q : ℕ)
    (x : continuousCohomology q (discreteUnitsRepresentation E Ω)) :
    ∃ (P : OpenNormalSubgroup Gal(Ω/K)) (hPE : P.toSubgroup ≤ E.fixingSubgroup),
      letI := fixedFieldRestrictedAlgebra K Ω E (FixedFieldRefinement.closed K Ω P) hPE
      ∃ y : relativeCohomology E (IntermediateField.fixedField P.toSubgroup) q,
        intermediateFixedFieldUnitInflation K Ω E P hPE q y = x := by
  let AH := (A).restrict E.fixingSubgroup
  let e := intermediateUnitCohomologyIso K Ω E q
  let : CompactSpace E.fixingSubgroup :=
    isCompact_iff_compactSpace.mp (H).isClosed.isCompact
  obtain ⟨P, z, hz⟩ := finiteStageToContinuous_jointly_surjective AH q (e.inv x)
  obtain ⟨N', hN'E, hN'P⟩ := exists_ambient_openNormal H P
  let NC' := FixedFieldRefinement.closed K Ω N'
  let := fixedFieldRestrictedAlgebra K Ω E NC' hN'E
  let := fixedFieldRestrictedTowerBase K Ω E NC' hN'E
  let := fixedFieldRestrictedTowerTop K Ω E NC' hN'E
  let eE := fixedFieldRestrictedCohomologyIso K Ω E NC' hN'E q
  let w := finiteInflation AH.toRep q hN'P z
  refine ⟨N', hN'E, eE.hom w, ?_⟩
  have hw := ConcreteCategory.congr_hom (finiteStageToContinuous_refinement AH hN'P q) z
  change finiteStageToContinuous AH (restrictOpenNormal H N') q w =
    finiteStageToContinuous AH P q z at hw
  change e.hom (finiteStageToContinuous AH (restrictOpenNormal H N') q
    (eE.inv (eE.hom w))) = x
  rw [Iso.hom_inv_id_apply, hw, hz, Iso.inv_hom_id_apply]

end Langlands.ClassFieldTheory.Local
