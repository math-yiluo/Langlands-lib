import Langlands.ClassFieldTheory.Local.AbsoluteH2InflationProof
import Langlands.ClassFieldTheory.Local.SeparableInertiaH2
import Langlands.Cohomology.Continuous.ClosedSubgroupDescentProof
import Langlands.Galois.Local.SeparableUnramifiedProof

/-! # Finite unramified inflation on actual separable unit cohomology -/

noncomputable section

open CategoryTheory Langlands.Continuous Langlands.LocalGalois.Separable
open scoped Topology

namespace Langlands.ClassFieldTheory.Local

universe u

section Galois

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The fixed field of an open normal subgroup is finite over the base. -/
theorem fixedField_openNormal_finiteDimensional (H : OpenNormalSubgroup Gal(L/K)) :
    FiniteDimensional K (IntermediateField.fixedField H.toSubgroup) := by
  apply (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField H.toSubgroup)).mp
  rw [show H.toSubgroup = (FixedFieldRefinement.closed K L H).toSubgroup from rfl,
    InfiniteGalois.fixingSubgroup_fixedField]
  exact H.toOpenSubgroup.isOpen

/-- Inflate an actual relative class of the fixed field to continuous unit
cohomology using the open normal quotient. -/
def fixedFieldUnitInflation (H : OpenNormalSubgroup Gal(L/K)) (q : ℕ) :
    relativeCohomology K (IntermediateField.fixedField H.toSubgroup) q ⟶
      (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).obj
        (continuousCohomology q (discreteUnitsRepresentation K L)) :=
  (fixedFieldCohomologyIso K L (FixedFieldRefinement.closed K L H) q).inv ≫
    finiteStageToContinuous (galoisUnitDiscreteModule K L) H q

set_option backward.isDefEq.respectTransparency false in
/-- Inflation from a finite stage factors through relative inflation to any
refining fixed field. -/
theorem fixedFieldUnitInflation_refinement {N H : OpenNormalSubgroup Gal(L/K)}
    (h : N ≤ H) (q : ℕ) :
    letI := FixedFieldRefinement.inclusionAlgebra h
    letI := FixedFieldRefinement.baseTower h
    relativeInflation K (IntermediateField.fixedField H.toSubgroup)
        (IntermediateField.fixedField N.toSubgroup) q ≫ fixedFieldUnitInflation K L N q =
      fixedFieldUnitInflation K L H q := by
  let := FixedFieldRefinement.inclusionAlgebra h
  let := FixedFieldRefinement.baseTower h
  let eH := fixedFieldCohomologyIso K L (FixedFieldRefinement.closed K L H) q
  let eN := fixedFieldCohomologyIso K L (FixedFieldRefinement.closed K L N) q
  have hi := FixedFieldRefinement.cohomology_inflation h q
  have href := finiteStageToContinuous_refinement (galoisUnitDiscreteModule K L) h q
  apply (cancel_epi eH.hom).mp
  change
    eH.hom ≫ _ ≫ eN.inv ≫ finiteStageToContinuous (galoisUnitDiscreteModule K L) N q =
      eH.hom ≫ eH.inv ≫ finiteStageToContinuous (galoisUnitDiscreteModule K L) H q
  rw [← Category.assoc eH.hom, ← hi, Category.assoc, eN.hom_inv_id_assoc,
    eH.hom_inv_id_assoc]
  exact href

set_option backward.isDefEq.respectTransparency false in
private theorem galoisUnitFiniteStageH2Exactness (H N : OpenNormalSubgroup Gal(L/K))
    (h : N ≤ H) :
    Function.Injective (finiteInflation (galoisUnitDiscreteModule K L).toRep 2 h) ∧
      LinearMap.range (finiteInflation (galoisUnitDiscreteModule K L).toRep 2 h).hom =
        LinearMap.ker (finiteRestriction (galoisUnitDiscreteModule K L)
          H.toOpenSubgroup N 2).hom := by
  let HC := FixedFieldRefinement.closed K L H
  let NC := FixedFieldRefinement.closed K L N
  let E := IntermediateField.fixedField H.toSubgroup
  let M := IntermediateField.fixedField N.toSubgroup
  let : FiniteDimensional K E := fixedField_openNormal_finiteDimensional K L H
  let : FiniteDimensional K M := fixedField_openNormal_finiteDimensional K L N
  let : IsGalois K E := IsGalois.of_fixedField_normal_subgroup H.toSubgroup
  let : IsGalois K M := IsGalois.of_fixedField_normal_subgroup N.toSubgroup
  have hfix : E.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField HC
  let HE : OpenSubgroup Gal(L/K) := ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩
  have hHE : H.toOpenSubgroup = HE := OpenSubgroup.toSubgroup_injective hfix.symm
  have hNE : NC.toSubgroup ≤ E.fixingSubgroup := hfix.symm ▸ h
  let := fixedFieldRestrictedAlgebra K L E NC hNE
  let := fixedFieldRestrictedTowerBase K L E NC hNE
  let := fixedFieldRestrictedTowerTop K L E NC hNE
  let ExactAt (J : OpenSubgroup Gal(L/K)) :=
    Function.Injective (finiteInflation (galoisUnitDiscreteModule K L).toRep 2 h) ∧
      LinearMap.range (finiteInflation (galoisUnitDiscreteModule K L).toRep 2 h).hom =
        LinearMap.ker (finiteRestriction (galoisUnitDiscreteModule K L) J N 2).hom
  change ExactAt H.toOpenSubgroup
  rw [hHE]
  apply AbsoluteH2Assembly.linearExactness_of_comparison
    (finiteInflation (galoisUnitDiscreteModule K L).toRep 2 h).hom
    (finiteRestriction (galoisUnitDiscreteModule K L) HE N 2).hom
    (relativeInflation K E M 2).hom
    (relativeRestriction K E M 2).hom
    (fixedFieldCohomologyIso K L HC 2).toLinearEquiv
    (fixedFieldCohomologyIso K L NC 2).toLinearEquiv
    (fixedFieldRestrictedCohomologyIso K L E NC hNE 2).toLinearEquiv
  · intro x
    exact ConcreteCategory.congr_hom (FixedFieldRefinement.cohomology_inflation h 2) x
  · intro x
    exact ConcreteCategory.congr_hom (fixedFieldRestrictedCohomologyIso_restriction K L E NC hNE 2) x
  · exact finiteRelativeH2InflationExactness K E M

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-field inflation in degree two is injective with image the kernel of
restriction to the open normal subgroup. -/
theorem fixedFieldUnitInflation_H2_exactness (H : OpenNormalSubgroup Gal(L/K)) :
    Function.Injective (fixedFieldUnitInflation K L H 2) ∧
      LinearMap.range (fixedFieldUnitInflation K L H 2).hom =
        LinearMap.ker ((forget₂ (TopModuleCat.{u} IntegerScalars.{u})
          (ModuleCat.{u} IntegerScalars.{u})).map
            (continuousRestriction (galoisUnitDiscreteModule K L) H.toSubgroup 2)).hom := by
  let e := fixedFieldCohomologyIso K L (FixedFieldRefinement.closed K L H) 2
  obtain ⟨hi, he⟩ := finiteStageExactnessLimit IntegerScalars.{u} Gal(L/K)
    (galoisUnitDiscreteModule K L) H 2 (galoisUnitFiniteStageH2Exactness K L H)
  refine ⟨hi.comp e.toLinearEquiv.symm.injective, ?_⟩
  change LinearMap.range ((finiteStageToContinuous (galoisUnitDiscreteModule K L) H 2).hom.comp
    e.inv.hom) = _
  have hinv : Function.Surjective e.inv.hom := e.toLinearEquiv.symm.surjective
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hinv)).trans he

end Galois

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

set_option backward.isDefEq.respectTransparency false in
/-- Every continuous class of separable-closure units inflates from the actual
relative cohomology of a finite Galois unramified intermediate field. -/
theorem exists_unramified_fixedFieldUnitInflation
    (x : continuousCohomology 2 (discreteUnitsRepresentation F (SeparableClosure F))) :
    ∃ H : OpenNormalSubgroup Gal(SeparableClosure F/F),
      ArithmeticUnramified F (IntermediateField.fixedField H.toSubgroup) ∧
        ∃ y : relativeCohomology F (IntermediateField.fixedField H.toSubgroup) 2,
          fixedFieldUnitInflation F (SeparableClosure F) H 2 y = x := by
  let A := galoisUnitDiscreteModule F (SeparableClosure F)
  let I : ClosedSubgroup Gal(SeparableClosure F/F) :=
    ⟨separableInertia F, separableInertia_isClosed F⟩
  let : I.toSubgroup.Normal := separableInertia_normal F
  have hIx : continuousRestriction A I.toSubgroup 2 x = 0 :=
    (separableInertiaH2_subsingleton F).elim _ _
  obtain ⟨H, hIH, hHx⟩ := exists_openNormal_continuousRestriction_zero A I 2 x hIx
  let E := IntermediateField.fixedField H.toSubgroup
  let : FiniteDimensional F E := fixedField_openNormal_finiteDimensional F (SeparableClosure F) H
  refine ⟨H, (finiteUnramifiedMaximality F E).mp (IntermediateField.fixedField_le hIH), ?_⟩
  have hx : x ∈ LinearMap.range (fixedFieldUnitInflation F (SeparableClosure F) H 2).hom := by
    rw [(fixedFieldUnitInflation_H2_exactness F (SeparableClosure F) H).2]
    exact LinearMap.mem_ker.mpr hHx
  exact hx

end Langlands.ClassFieldTheory.Local
