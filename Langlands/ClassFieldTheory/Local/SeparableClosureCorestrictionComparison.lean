import Langlands.Algebra.BrauerComparison.SeparableFiniteStages
import Langlands.ClassFieldTheory.Local.SeparableClosureCorestrictionStages

/-! # Finite-stage inflation for the absolute transfer comparison -/

noncomputable section

open CategoryTheory Langlands.Continuous Langlands.BrauerComparison

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

private abbrev forgetComparisonUnits :
    TopModuleCat.{u} IntegerScalars.{u} ⥤ ModuleCat.{u} IntegerScalars.{u} :=
  forget₂ _ _

section Lower

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (N : OpenNormalSubgroup Gal(Ω/K))

/-- Lower fixed-field inflation is the finite relative inflation used by
the comparison with Brauer classes. -/
theorem fixedFieldUnitInflation_eq_relativeToContinuous (q : ℕ)
    (x : relativeCohomology K (galoisFixedStage K Ω N) q) :
    fixedFieldUnitInflation K Ω N q x = relativeToContinuous K (galoisFixedStage K Ω N) Ω q x := by
  let e := galoisFixedStageIso K Ω N q
  have h := finiteStageToContinuous_eq_relativeToContinuous K Ω N q (e.inv x)
  change fixedFieldUnitInflation K Ω N q x =
    relativeToContinuous K (galoisFixedStage K Ω N) Ω q x
  rw [Iso.inv_hom_id_apply] at h
  exact h

end Lower

section Containment

variable (K L F : Type u) [Field K] [Field L] [Field F] [Algebra K L] [Algebra L F]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [FiniteDimensional L F]

local notation "S" => SeparableClosure K
local notation "T" => SeparableClosure L

/-- An embedded finite extension of the upper base is contained in an
ambient finite Galois stage with the same embedding into its closure. -/
theorem exists_separableClosureStage_containing (i : F →ₐ[L] T) :
    ∃ (N : OpenNormalSubgroup Gal(S/K)) (h : N.toSubgroup ≤ (separableClosureBase K L).fixingSubgroup),
      let M := separableClosureStageField K N
      letI := separableClosureStageAlgebra K L N h
      letI := separableClosureStageTopAlgebra K L N
      ∃ j : F →ₐ[L] M, ∀ x, algebraMap M T (j x) = i x := by
  let : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K F := FiniteDimensional.trans K L F
  let e := separableClosureTowerEquiv K L
  let p : F →ₐ[K] S := e.symm.toAlgHom.comp (i.restrictScalars K)
  let C := p.fieldRange
  let b := AlgEquiv.ofInjective p p.injective
  let : FiniteDimensional K C := Module.Finite.equiv b.toLinearEquiv
  let H := intermediateFieldFixingOpenSubgroup K S C
  let N := ambientOpenNormalCore H
  have hNC : N.toSubgroup ≤ C.fixingSubgroup := ambientOpenNormalCore_le H
  have hEC : separableClosureBase K L ≤ C := by
    rintro _ ⟨a, rfl⟩
    refine ⟨algebraMap L F a, ?_⟩
    change e.symm (i (algebraMap L F a)) = e.symm (algebraMap L T a)
    rw [i.commutes]
  have h : N.toSubgroup ≤ (separableClosureBase K L).fixingSubgroup :=
    hNC.trans (IntermediateField.fixingSubgroup_le hEC)
  let M := separableClosureStageField K N
  let := separableClosureStageAlgebra K L N h
  let := separableClosureStageTopAlgebra K L N
  have hCM : C ≤ M :=
    le_fixedField_of_le_fixingSubgroup K S C (FixedFieldRefinement.closed K S N) hNC
  let jK : F →ₐ[K] M := (IntermediateField.inclusion hCM).comp b.toAlgHom
  let j : F →ₐ[L] M :=
    { jK.toRingHom with
      commutes' := by
        intro a
        apply Subtype.ext
        change e.symm (i (algebraMap L F a)) = e.symm (algebraMap L T a)
        rw [i.commutes] }
  refine ⟨N, h, j, ?_⟩
  intro x
  change e (e.symm (i x)) = i x
  exact e.apply_symm_apply _

end Containment

section Upper

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (N : OpenNormalSubgroup Gal(SeparableClosure K/K))
  (h : N.toSubgroup ≤ (separableClosureBase K L).fixingSubgroup)

local notation "S" => SeparableClosure K
local notation "T" => SeparableClosure L
local notation "E" => separableClosureBase K L
local notation "M" => separableClosureStageField K N
local notation "C" => FixedFieldRefinement.closed K S N
local notation "H" => intermediateFieldFixingOpenSubgroup K S E
local notation "P" => restrictOpenNormal H N
set_option quotPrecheck false in
local notation "AH" => (galoisUnitDiscreteModule K S).restrict (E).fixingSubgroup
local notation "V" => discreteUnitsRepresentation L M

set_option maxHeartbeats 1200000 in
/-- The upper finite-stage map of absolute corestriction is the relative
inflation on the original upper field, as used by the Brauer comparison. -/
theorem separableClosureStageUnitInflation_eq_relativeToContinuous (q : ℕ) :
    letI := separableClosureStageAlgebra K L N h
    letI := separableClosureStageTowerBase K L N h
    letI := separableClosureStageTopAlgebra K L N
    letI := separableClosureStageTowerTop K L N h
    letI := fixedField_openNormal_finiteDimensional K S N
    letI : FiniteDimensional L M := FiniteDimensional.right K L M
    letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    ∀ x : relativeCohomology L M q,
      separableClosureStageUnitInflation K L N h q x = relativeToContinuous L M T q x := by
  let := separableClosureStageAlgebra K L N h
  let := separableClosureStageTowerBase K L N h
  let := separableClosureStageTopAlgebra K L N
  let := separableClosureStageTowerTop K L N h
  let := fixedField_openNormal_finiteDimensional K S N
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let := fixedFieldRestrictedAlgebra K S E (C) h
  let := fixedFieldRestrictedTowerBase K S E (C) h
  let := fixedFieldRestrictedTowerTop K S E (C) h
  let : Normal E M := Normal.tower_top_of_normal K E M
  let : IsTopologicalGroup (H) := inferInstanceAs (IsTopologicalGroup (E).fixingSubgroup)
  let : DiscreteTopology ((E).fixingSubgroup ⧸ (P).toSubgroup) :=
    QuotientGroup.discreteTopology (P).toOpenSubgroup.isOpen
  let := continuousToOrdinary_isIso V q
  let b := separableClosureBaseEquiv K L
  let hb := separableClosureStageAlgebra_apply K L N h
  let eBase := relativeBaseFieldAutEquiv b hb
  let eQ : ((E).fixingSubgroup ⧸ (P).toSubgroup) ≃* Gal(M/L) :=
    (fixedFieldRestrictedGroupEquiv K S E (C)).trans eBase.symm
  let eU := fixedFieldRestrictedUnitsEquiv K S E (C) h
  have heQ (σ : (E).fixingSubgroup) (x : M) :
      ((eQ (QuotientGroup.mk σ) x : M) : S) = σ.val (x : S) :=
    (IntermediateField.fixingSubgroupEquiv (E) σ).restrictNormal_commutes M x
  have heU (g : (E).fixingSubgroup ⧸ (P).toSubgroup) :
      eU.toLinearMap ∘ₗ (finiteQuotientRep (AH).toRep (P)).ρ g =
        ((V).ρ (eQ g)).toLinearMap ∘ₗ eU.toLinearMap := by
    exact fixedFieldRestrictedUnitsEquiv_intertwines K S E (C) h g
  let φ : (E).fixingSubgroup →ₜ* Gal(M/L) :=
    { __ := eQ.toMonoidHom.comp (quotientProjection P).toMonoidHom
      continuous_toFun := (continuous_of_discreteTopology :
        Continuous (eQ : ((E).fixingSubgroup ⧸ (P).toSubgroup) → Gal(M/L))).comp
          (quotientProjection P).continuous }
  let f : TopRep.res φ V ⟶ (AH).toTopRep :=
    TopRep.ofHom
      { toContinuousLinearMap :=
          { toLinearMap := unitInclusionLinear M S
            cont := continuous_of_discreteTopology }
        isIntertwining' σ := by
          apply ContinuousLinearMap.ext
          intro x
          apply Units.ext
          exact heQ σ x.val }
  let e₁ := fixedFieldRestrictedCohomologyIso K S E (C) h q
  let e₂ := relativeBaseFieldCohomologyIso b hb q
  let eStage := groupCohomology.mapIso
    (A := Rep.of (V).ρ.toRepresentation) (B := finiteQuotientRep (AH).toRep (P)) eQ eU heU q
  have hReindex : eStage.hom = e₁.hom ≫ e₂.inv := by
    change eStage.hom =
      (fixedFieldRestrictedCohomologyIso K S E (C) h q).hom ≫
        (relativeBaseFieldCohomologyIso b hb q).inv
    unfold eStage fixedFieldRestrictedCohomologyIso relativeBaseFieldCohomologyIso
    rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom, groupCohomology.mapIso_inv,
      ← groupCohomology.map_comp]
    apply groupCohomology.map_congr
    · rfl
    · rfl
  let f₁ := intermediateUnitCohomologyIso K S E q
  let f₂ := separableClosureUpperUnitIso K L q
  have hCont : ContinuousCohomology.map φ f q ≫ f₁.hom ≫ f₂.hom =
      continuousUnitInflation L M T q := by
    change ContinuousCohomology.map φ f q ≫
      (intermediateUnitCohomologyIso K S E q).hom ≫
      (separableClosureUpperUnitIso K L q).hom = _
    unfold intermediateUnitCohomologyIso separableClosureUpperUnitIso unitCohomologyIsoOfRingEquiv
      continuousUnitInflation
    rw [continuousCohomologyIso_hom, continuousCohomologyIso_hom,
      ← ContinuousCohomology.map_comp, ← ContinuousCohomology.map_comp]
    apply congrArg (fun t => HomologicalComplex.homologyMap t q)
    apply continuousCochainsMap_congr
    · apply ContinuousMonoidHom.ext
      intro σ
      apply AlgEquiv.ext
      intro x
      let e := (separableClosureTowerEquiv K L).toRingEquiv
      let b' := b.symm.toRingEquiv
      let he := separableClosureTowerEquiv_base K L
      let τ := (krullAutContinuousEquiv b' e he).symm σ
      apply (algebraMap M T).injective
      change e ((eQ (QuotientGroup.mk (fixingSubgroupContinuousEquiv (E) τ)) x : M) : S) =
        algebraMap M T ((σ.restrictNormal M) x)
      rw [heQ]
      exact (krullAutContinuousEquiv_symm_apply b' e he σ (x : S)).trans
        (AlgEquiv.restrictNormal_commutes σ M x).symm
    · intro x
      apply Units.ext
      rfl
  let F := forgetComparisonUnits
  have hStage : finiteStageToContinuous (AH) (P) q = eStage.hom ≫
      inv (continuousToOrdinary V q) ≫ F.map (ContinuousCohomology.map φ f q) :=
    finiteStageToContinuous_eq_mapIso (AH) (P) V eQ eU heU φ f (fun _ => rfl)
      (fun x => by apply Units.ext; rfl) q
  rw [hReindex] at hStage
  intro x
  let m := e₂.hom ≫ e₁.inv ≫ finiteStageToContinuous (AH) (P) q ≫ F.map f₁.hom ≫ F.map f₂.hom
  change m x = _
  have hm : m = inv (continuousToOrdinary V q) ≫ F.map (continuousUnitInflation L M T q) := by
    unfold m
    rw [hStage]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp, hCont]
  rw [hm]
  rfl

/-- On the relative cohomology classes used by the Brauer comparison,
absolute transfer is computed by ordinary finite Galois transfer. -/
theorem separableUnitCorestriction_relativeToContinuous (q : ℕ) [NeZero q] :
    letI := separableClosureStageAlgebra K L N h
    letI := separableClosureStageTowerBase K L N h
    letI := separableClosureStageTopAlgebra K L N
    letI := separableClosureStageTowerTop K L N h
    letI := fixedField_openNormal_finiteDimensional K S N
    letI : FiniteDimensional L M := FiniteDimensional.right K L M
    letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    ∀ x : relativeCohomology L M q,
      separableUnitCorestriction K L q (relativeToContinuous L M T q x) =
        relativeToContinuous K M S q (relativeCorestriction K L M q x) := by
  let := separableClosureStageAlgebra K L N h
  let := separableClosureStageTowerBase K L N h
  let := separableClosureStageTopAlgebra K L N
  let := separableClosureStageTowerTop K L N h
  let := fixedField_openNormal_finiteDimensional K S N
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  intro x
  have hc := ConcreteCategory.congr_hom
    (separableClosureStageUnitInflation_corestriction K L N h q) x
  change separableUnitCorestriction K L q (separableClosureStageUnitInflation K L N h q x) =
    fixedFieldUnitInflation K S N q (relativeCorestriction K L M q x) at hc
  rw [separableClosureStageUnitInflation_eq_relativeToContinuous,
    fixedFieldUnitInflation_eq_relativeToContinuous] at hc
  exact hc

end Upper

end Langlands.ClassFieldTheory.Local
