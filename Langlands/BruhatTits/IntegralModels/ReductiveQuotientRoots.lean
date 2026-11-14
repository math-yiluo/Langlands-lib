import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Lie.TargetCoefficients
import Langlands.GroupScheme.CentralIsogeny.CenterTangentQuotient

/-! # Root survival in the actual reductive special-fibre quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

local instance reductiveQuotientRoots_neutralAffine (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance reductiveQuotientRoots_neutralFiniteType (D : RelativeComponentModelData R K G) :
    LocallyOfFiniteType D.neutral.specialFibre.X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G}
  (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

include hQ

/-- The supplied reductive-quotient projection is smooth because its actual
represented radical is smooth. -/
theorem projection_smooth : Smooth Q.projection.hom.hom.left := by
  have hqc : QuasiCompact (Q.projection.hom.hom.left ≫ Q.quotient.X.hom) := by
    rw [Over.w Q.projection.hom.hom]
    infer_instance
  let : QuasiCompact (Q.projection.hom.hom.left ≫ Q.quotient.X.hom) := hqc
  let : QuasiCompact Q.projection.hom.hom.left :=
    QuasiCompact.of_comp Q.projection.hom.hom.left Q.quotient.X.hom
  let : IsClosedImmersion Q.radicalInclusion.hom.hom.left := hQ.1.isClosedSubgroup
  let : Mono Q.radicalInclusion.hom.hom := Over.mono_of_mono_left _
  exact hQ.2.1.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hQ.1.smooth

/-- The differential kernel is exactly the tangent submodule of the supplied
radical's all-test image. -/
theorem ker_projection_eq_radical_lie :
    LinearMap.ker (Lie.targetMapLinear Q.projection (IsLocalRing.ResidueField R)) =
      (SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R) := by
  rw [← lie_range_kernelι_eq_ker_targetMapLinear, hQ.2.1.2.2.2]

variable {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)

include hT

/-- Every special-fibre adjoint weight maps onto the same weight of the
actual reductive quotient. This includes the zero character. -/
theorem map_weightSpace_eq (χ : characterLattice T.specialFibre) :
    (weightSpace T.specialFibreInclusion χ).map
        (Lie.targetMapLinear Q.projection (IsLocalRing.ResidueField R)) =
      weightSpace (T.specialFibreInclusion ≫ Q.projection) χ := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact lieKernelHomLinear_mem_weightSpace Q.projection T.specialFibreInclusion χ hY
  · intro hX
    obtain ⟨Y, hY⟩ := Lie.targetMapLinear_surjective_of_smooth Q.projection
      (IsLocalRing.ResidueField R) (Q.projection_smooth hQ) X
    exact Lie.exists_weightSpace_preimage Q.projection T.specialFibreInclusion
      (hT.baseChange (IntegralModel.residueBaseMap R)) hX ⟨Y, hY⟩

/-- Each actual quotient weight space is canonically the source weight
space modulo the kernel of its restricted differential. -/
def weightSpaceQuotientEquiv (χ : characterLattice T.specialFibre) :
    (weightSpace T.specialFibreInclusion χ ⧸
        LinearMap.ker (Lie.weightSpaceMap Q.projection T.specialFibreInclusion χ)) ≃ₗ[
          IsLocalRing.ResidueField R]
      weightSpace (T.specialFibreInclusion ≫ Q.projection) χ :=
  LinearMap.quotKerEquivOfSurjective _ (by
    intro X
    have hX : (X : Additive (lieKernel Q.quotient (IsLocalRing.ResidueField R))) ∈
        (weightSpace T.specialFibreInclusion χ).map
          (Lie.targetMapLinear Q.projection (IsLocalRing.ResidueField R)) := by
      rw [Q.map_weightSpace_eq hQ T hT χ]
      exact X.property
    obtain ⟨Y, hY, hYX⟩ := hX
    exact ⟨⟨Y, hY⟩, Subtype.ext hYX⟩)

/-- A weight disappears in the reductive quotient exactly when its whole
source weight space lies in the actual radical's tangent image. -/
theorem weightSpace_eq_bot_iff_le_radical_lie (χ : characterLattice T.specialFibre) :
    weightSpace (T.specialFibreInclusion ≫ Q.projection) χ = ⊥ ↔
      weightSpace T.specialFibreInclusion χ ≤
        (SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R) := by
  rw [← Q.map_weightSpace_eq hQ T hT χ, ← LinearMap.le_ker_iff_map,
    Q.ker_projection_eq_radical_lie hQ]

/-- The roots of the actual quotient are precisely the nonzero characters
whose source weight space is not contained in the actual radical's Lie image. -/
theorem mem_relativeRoots_iff_not_le_radical_lie (χ : characterLattice T.specialFibre) :
    χ ∈ relativeRoots (T.specialFibreInclusion ≫ Q.projection) ↔
      χ ≠ 0 ∧ ¬ weightSpace T.specialFibreInclusion χ ≤
        (SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R) := by
  exact and_congr Iff.rfl
    (not_congr (Q.weightSpace_eq_bot_iff_le_radical_lie hQ T hT χ))

/-- A reductive-quotient root is already a root of the neutral special fibre,
on the same actual special-fibre torus. -/
theorem relativeRoots_subset_specialFibre :
    relativeRoots (T.specialFibreInclusion ≫ Q.projection) ⊆
      relativeRoots T.specialFibreInclusion := by
  intro χ hχ
  obtain ⟨hχ0, hχN⟩ := (Q.mem_relativeRoots_iff_not_le_radical_lie hQ T hT χ).mp hχ
  refine ⟨hχ0, ?_⟩
  intro hbot
  apply hχN
  rw [hbot]
  exact bot_le

end SpecialFibreQuotientData
end Langlands.BruhatTits.IntegralModels
