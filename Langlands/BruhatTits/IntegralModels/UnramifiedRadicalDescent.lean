import Langlands.BruhatTits.IntegralModels.SpecialFibrePositiveDescent
import Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalProof
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Mathlib.FieldTheory.Perfect

/-! # Actual unipotent radicals in unramified special fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 80000

namespace Langlands.GroupScheme

/-- Identify the point kernel after an ambient isomorphism from an all-test
kernel-range equality. -/
theorem rationalPoints_kernel_iso {k : Type u} [Field k]
    {A B H U : GroupScheme (Spec (CommRingCat.of k))}
    (e : A ≅ B) (j : U ⟶ B) (q : B ⟶ H)
    (h : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j) :
    (rationalPoints.map (e.hom ≫ q)).ker =
      (rationalPoints.map (j ≫ e.inv)).range := by
  ext x
  change x ≫ (e.hom ≫ q).hom.hom = 1 ↔
    x ∈ (SubgroupFunctor.range (j ≫ e.symm.hom)).carrier _
  rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.mem_comap]
  rw [← h, mem_range_kernelι_iff]
  change x ≫ (e.hom.hom.hom ≫ q.hom.hom) = 1 ↔
    (x ≫ e.hom.hom.hom) ≫ q.hom.hom = 1
  rw [Category.assoc]

end Langlands.GroupScheme

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

/-- Compare the actual special fibre upstairs with the residue scalar extension
of the original special fibre, using the square underlying the extended map. -/
def unramifiedSpecialFibreIso :
    M.baseChangeUnramified.specialFibre ≅
      (GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj M.specialFibre :=
  Descent.squareComparison
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (residueBaseMap (fixedFieldIntegers F))
    (residueBaseMap ↥𝒪[F])
    (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
    unramifiedResidue_specMap_comp M.group

/-- The published extended special-fibre map uses this same comparison. -/
theorem unramifiedSpecialFibreMap_eq
    {H : GroupScheme (Spec (CommRingCat.of 𝓀[F]))}
    (q : M.specialFibre ⟶ H) :
    M.unramifiedSpecialFibreMap q = M.unramifiedSpecialFibreIso.hom ≫
      (GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map q := by
  unfold unramifiedSpecialFibreMap
  rw [Descent.squareComparisonMap_def]
  rfl

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

open GroupScheme Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {D : RelativeComponentModelData ↥𝒪[F] F G} (Q : SpecialFibreQuotientData D)

local instance :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

/-- There is an actual unipotent radical of the actual special fibre upstairs,
and the extended quotient-kernel subgroup is its reduction preimage image. -/
theorem exists_unramifiedRadical (hQ : Q.IsReductiveQuotient) :
    ∃ (U : GroupScheme
        (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : U ⟶ D.neutral.baseChangeUnramified.specialFibre),
      IsUnipotentRadical i ∧
        Q.unramifiedKernelPoints =
          (((rationalPoints.map i).range.comap
            D.neutral.baseChangeUnramified.reduction).map
              D.neutral.baseChangeUnramified.integralPointMap) := by
  let b := Spec.algebraMap 𝓀[F]
    (IsLocalRing.ResidueField (fixedFieldIntegers F))
  let e := D.neutral.unramifiedSpecialFibreIso
  let j := (GroupScheme.baseChange b).map Q.radicalInclusion
  let q := (GroupScheme.baseChange b).map Q.projection
  let i := j ≫ e.inv
  let : Module.IsTorsionFree 𝓀[F]
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    DivisionSemiring.to_moduleIsTorsionFree
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : Algebra.IsSeparable 𝓀[F]
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) := inferInstance
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : Smooth D.neutral.specialFibre.X.hom := by
    change Smooth (pullback.snd D.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  let : IsAffineHom D.neutral.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd D.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  let : ConnectedSpace D.neutral.specialFibre.X.left :=
    D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres
  have hj : IsUnipotentRadical j :=
    SeparableUnipotentRadical.isUnipotentRadical_baseChange hQ.1
  refine ⟨(GroupScheme.baseChange b).obj Q.radical, i, hj.comp_iso e.symm, ?_⟩
  have hquot : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q := by
    simpa only [j, q, SubgroupFunctor.range_baseChangeHom] using
      hQ.2.1.baseChange b
  have hker : (rationalPoints.map
      (D.neutral.unramifiedSpecialFibreMap Q.projection)).ker =
        (rationalPoints.map i).range := by
    rw [D.neutral.unramifiedSpecialFibreMap_eq]
    exact rationalPoints_kernel_iso e j q hquot.2.2.2
  change (((rationalPoints.map
      (D.neutral.unramifiedSpecialFibreMap Q.projection)).comp
        D.neutral.baseChangeUnramified.reduction).ker.map
          D.neutral.baseChangeUnramified.integralPointMap) = _
  change ((rationalPoints.map
      (D.neutral.unramifiedSpecialFibreMap Q.projection)).ker.comap
        D.neutral.baseChangeUnramified.reduction).map
          D.neutral.baseChangeUnramified.integralPointMap = _
  rw [hker]

end Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData
