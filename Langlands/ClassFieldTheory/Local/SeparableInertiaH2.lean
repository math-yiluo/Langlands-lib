import Langlands.ClassFieldTheory.Local.ClosureCoefficients
import Langlands.ClassFieldTheory.Local.FiniteNormH2Proof
import Langlands.ClassFieldTheory.Local.FixedFieldUnits
import Langlands.ClassFieldTheory.Local.SeparableInertiaFullNorm
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormProof
import Langlands.Cohomology.Continuous.EquivalenceTransport
import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof

/-! # Vanishing of continuous H² of separable inertia -/

noncomputable section

open CategoryTheory Langlands.Continuous Langlands.LocalGalois.Separable
open scoped NNReal Topology

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The actual unit action in the jointly continuous discrete module used for
finite quotient comparison. -/
def galoisUnitDiscreteModule (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : DiscreteModule IntegerScalars.{u} Gal(L/K) where
  toTopRep := discreteUnitsRepresentation K L
  isDiscrete := inferInstance
  continuous_action := continuous_unitAction K L

private theorem continuous_fixingSubgroupEquiv_symm
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (E : IntermediateField K L) :
    Continuous E.fixingSubgroupEquiv.symm := by
  apply Continuous.subtype_mk
  change Continuous (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K))
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro V hV
  rw [map_one, krullTopology_mem_nhds_one_iff] at hV
  obtain ⟨M, hM, hMV⟩ := hV
  let := hM
  obtain ⟨s, hs⟩ := (IntermediateField.essFiniteType_iff (K := M)).mp inferInstance
  let N := IntermediateField.adjoin E (s : Set L)
  have : FiniteDimensional E N :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  apply (krullTopology_mem_nhds_one_iff E L _).mpr
  refine ⟨N, inferInstance, ?_⟩
  intro σ hσ
  apply hMV
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hs]
  apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff K (σ.restrictScalars K)).mpr
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff N σ).mp hσ x
    (IntermediateField.subset_adjoin E _ hx)

/-- The Krull topology on the subgroup fixing an intermediate field is the
Krull topology on the Galois group over that field. -/
def fixingSubgroupContinuousEquiv {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (E : IntermediateField K L) : Gal(L/E) ≃ₜ* E.fixingSubgroup := by
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  exact
    { E.fixingSubgroupEquiv.symm with
      continuous_toFun := continuous_fixingSubgroupEquiv_symm E
      continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
        (f := E.fixingSubgroupEquiv.symm.toEquiv) (continuous_fixingSubgroupEquiv_symm E) }

private def fixingSubgroupUnitIso {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (E : IntermediateField K L) :
    TopRep.res (fixingSubgroupContinuousEquiv E : Gal(L/E) →ₜ* E.fixingSubgroup)
      (TopRep.res E.fixingSubgroup.subtype (discreteUnitsRepresentation K L)) ≅
        discreteUnitsRepresentation E L where
  hom.hom' :=
    { toContinuousLinearMap := { toLinearMap := LinearMap.id, cont := continuous_id }
      isIntertwining' _ := rfl }
  inv.hom' :=
    { toContinuousLinearMap := { toLinearMap := LinearMap.id, cont := continuous_id }
      isIntertwining' _ := rfl }
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

private theorem ambientNorm_relativeH2_subsingleton
    {U L : Type u} [Field U] [Field L] [Algebra U L] [IsGalois U L]
    {w : Valuation L ℝ≥0} (h : SeparableInertiaNorm.AmbientHyp (U := U) w)
    (M : IntermediateField U L) [FiniteDimensional U M] [IsGalois U M] :
    Subsingleton (relativeCohomology U M 2) := by
  apply finiteNormH2Vanishing U M
  intro E
  let : FiniteDimensional U E := FiniteDimensional.left U E M
  let : FiniteDimensional E M := FiniteDimensional.right U E M
  let : IsGalois E M := IsGalois.tower_top_of_isGalois U E M
  exact h.surjective_unit_norm (E := E) (M := M)

private theorem continuousH2_subsingleton_of_finiteRelative
    (U L : Type u) [Field U] [Field L] [Algebra U L] [IsGalois U L]
    (hfinite : ∀ (M : IntermediateField U L) [FiniteDimensional U M] [IsGalois U M],
      Subsingleton (relativeCohomology U M 2)) :
    Subsingleton (continuousCohomology 2 (discreteUnitsRepresentation U L)) := by
  let A := galoisUnitDiscreteModule U L
  have hstage (N : OpenNormalSubgroup Gal(L/U)) :
      Subsingleton (groupCohomology (finiteQuotientRep A.toRep N) 2) := by
    let H : ClosedSubgroup Gal(L/U) := ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩
    let : H.Normal := N.isNormal'
    let M := IntermediateField.fixedField H.toSubgroup
    have hopen : IsOpen (M.fixingSubgroup : Set Gal(L/U)) := by
      rw [InfiniteGalois.fixingSubgroup_fixedField H]
      exact N.toOpenSubgroup.isOpen
    let : FiniteDimensional U M := (InfiniteGalois.isOpen_iff_finite M).mp hopen
    let : IsGalois U M := IsGalois.of_fixedField_normal_subgroup H.toSubgroup
    let := hfinite M
    exact (fixedFieldCohomologyIso U L H 2).toLinearEquiv.injective.subsingleton
  have hz : Limits.IsZero (finiteQuotientCohomology A.toRep 2) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    apply Limits.colimit.hom_ext
    intro N
    let := hstage (OrderDual.ofDual N)
    exact (ModuleCat.isZero_of_subsingleton
      (groupCohomology (finiteQuotientRep A.toRep (OrderDual.ofDual N)) 2)).eq_of_src _ _
  let := ModuleCat.subsingleton_of_isZero hz
  exact (finiteQuotientComparisonLinearEquiv A 2).symm.injective.subsingleton

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

private theorem inertiaFixedFieldH2_subsingleton :
    Subsingleton (continuousCohomology 2
      (discreteUnitsRepresentation (inertiaFixedField F) (SeparableClosure F))) :=
  continuousH2_subsingleton_of_finiteRelative (inertiaFixedField F) (SeparableClosure F)
    (fun M => ambientNorm_relativeH2_subsingleton
      (SeparableInertiaNorm.ambientHyp_sepClosureValuation F) M)

/-- The actual separable inertia subgroup has trivial continuous H² with the
restricted discrete action on separable-closure units. -/
theorem separableInertiaH2_subsingleton :
    Subsingleton (continuousCohomology 2
      (TopRep.res (separableInertia F).subtype
        (discreteUnitsRepresentation F (SeparableClosure F)))) := by
  rw [← fixingSubgroup_inertiaFixedField F]
  let := inertiaFixedFieldH2_subsingleton F
  exact (Langlands.Continuous.continuousCohomologyIso
    (fixingSubgroupContinuousEquiv (inertiaFixedField F))
    (fixingSubgroupUnitIso (inertiaFixedField F)) 2).toContinuousLinearEquiv.injective.subsingleton

end Langlands.ClassFieldTheory.Local
