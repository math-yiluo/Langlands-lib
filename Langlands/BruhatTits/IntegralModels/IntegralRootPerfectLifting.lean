import Langlands.BruhatTits.IntegralModels.IntegralRootQuotientLifting
import Langlands.BruhatTits.IntegralModels.IntegralRootReduction
import Langlands.GroupScheme.Rational.PerfectRootQuotientLifting
import Langlands.GroupScheme.Rational.RootPointOutsideCyclicTail

/-! # Integral root lifts and higher-multiple exclusion over perfect residue fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry.Building
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

namespace IntegralTorusData

variable (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

local instance : Smooth D.neutral.group.X.hom := D.neutral_smooth

local instance : IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance : Smooth D.neutral.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

include hT hQ in
/-- Every actual quotient-root point lifts to an integral neutral-model
section whose generic point belongs to the corresponding original root group. -/
theorem exists_integral_root_quotient_lift_of_perfectResidue (a : characterLattice S) (ha : a ≠ 0)
    (g : rationalPoints Q.quotient)
    (hg : g ∈ (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT a)).carrier _) :
    ∃ x : D.neutral.integralSections,
      D.neutral.integralPointMap x ∈ rootGroupPoints i a ∧
        rationalPoints.map Q.projection (D.neutral.reduction x) = g := by
  let χ := (T.genericCharacterEquiv hT).symm a
  have hχ : χ ≠ 0 := by
    intro h
    apply ha
    have he := (T.genericCharacterEquiv hT).apply_symm_apply a
    change T.genericCharacterEquiv hT χ = a at he
    rw [h, map_zero] at he
    exact he.symm
  have hχa : T.genericCharacter χ = a :=
    (T.genericCharacterEquiv hT).apply_symm_apply a
  have hχs : T.characterSpecialization hT a = T.specialCharacter χ := by
    rw [← hχa, T.characterSpecialization_genericCharacter hT χ]
  let M := IntegralModel.SplitRoot.model D.neutral hT T.inclusion χ hχ
  let j : M.Hom D.neutral
      (IntegralModel.SplitRoot.genericHom D.neutral hT T.inclusion χ hχ) :=
    IntegralModel.SplitRoot.inclusion D.neutral hT T.inclusion χ hχ
  have hrep : (RelativeRoot.subgroup T.specialFibreInclusion
      (T.specialCharacter χ)).IsRepresentedBy j.specialFibreMap := by
    have hp := (IntegralModel.SplitRoot.integral_properties
      D.neutral hT T.inclusion χ hχ).1.baseChange (IntegralModel.residueBaseMap R)
    rw [← RelativeRoot.subgroup_baseChange] at hp
    exact hp
  have hχs0 : T.specialCharacter χ ≠ 0 := by
    intro hz
    apply hχ
    apply (T.specialCharacterEquiv hT).injective
    change T.specialCharacter χ = T.specialCharacter 0
    simpa only [map_zero] using hz
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  rw [hχs] at hg
  obtain ⟨v, hv, hvg⟩ := RelativeRoot.exists_root_point_lift_of_smooth_of_perfectField
    T.specialFibreInclusion (T.specialCharacter χ) Q.projection
    (hT.baseChange (IntegralModel.residueBaseMap R)) hχs0
    (Q.projection_smooth hQ) g hg
  rw [← hrep.2] at hv
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hv
  obtain ⟨z, hz⟩ := M.reduction_surjective
    (IntegralModel.SplitRoot.model_isSmooth D.neutral hT T.inclusion χ hχ) w
  refine ⟨rationalPoints.map j.hom z, ?_, ?_⟩
  · rw [j.integralPointMap_naturality]
    have hr : (RelativeRoot.subgroup i a).IsRepresentedBy
        (IntegralModel.SplitRoot.genericHom D.neutral hT T.inclusion χ hχ) := by
      rw [← hχa, ← T.generic_rootFunctor_eq χ]
      exact IntegralModel.SplitRoot.isRepresentedBy_genericHom
        D.neutral hT T.inclusion χ hχ
    change rationalPoints.map
      (IntegralModel.SplitRoot.genericHom D.neutral hT T.inclusion χ hχ)
      (M.integralPointMap z) ∈ (RelativeRoot.subgroup i a).carrier _
    rw [← hr.2]
    exact ⟨M.integralPointMap z, rfl⟩
  · rw [j.reduction_naturality, hz]
    change (w ≫ j.specialFibreMap.hom.hom) ≫ Q.projection.hom.hom = g
    rw [hw]
    exact hvg

/-- A chosen actual integral section lifting a quotient-root point, with
its generic point in the original root group. -/
def perfectResidueRootQuotientLift (a : characterLattice S) (ha : a ≠ 0)
    (g : (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT a)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))))) :
    D.neutral.integralSections :=
  Classical.choose (T.exists_integral_root_quotient_lift_of_perfectResidue hT Q hQ a ha g g.property)

theorem perfectResidueRootQuotientLift_spec (a : characterLattice S) (ha : a ≠ 0)
    (g : (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT a)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))))) :
    D.neutral.integralPointMap (T.perfectResidueRootQuotientLift hT Q hQ a ha g) ∈ rootGroupPoints i a ∧
      rationalPoints.map Q.projection
        (D.neutral.reduction (T.perfectResidueRootQuotientLift hT Q hQ a ha g)) = g :=
  Classical.choose_spec (T.exists_integral_root_quotient_lift_of_perfectResidue hT Q hQ a ha g g.property)


include hT hQ in
/-- An actual quotient root has an integral generic-root witness outside
every specified higher multiple, both generically and in quotient reduction. -/
theorem exists_integral_root_point_outside_nsmul_of_perfectResidue
    {a : characterLattice S}
    (ha : T.characterSpecialization hT a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : D.neutral.integralSections,
      D.neutral.integralPointMap x ∈ rootGroupPoints i a ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∈
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (T.characterSpecialization hT a)).carrier _ ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∉
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (n • T.characterSpecialization hT a)).carrier _ ∧
      D.neutral.integralPointMap x ∉ rootGroupPoints i (n • a) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hs := hT.baseChange (IntegralModel.residueBaseMap R)
  have ha0 : a ≠ 0 := by
    intro hz
    apply ha.1
    rw [hz, map_zero]
  have hna0 : n • a ≠ 0 := by
    intro hz
    apply hs.nsmul_ne_zero ha.1 (show n ≠ 0 by omega)
    rw [← map_nsmul, hz, map_zero]
  obtain ⟨g, hg, hgn⟩ := RelativeRoot.exists_rootPoint_not_mem_nsmul_of_field
    hs (T.specialFibreInclusion ≫ Q.projection) ha hn
  obtain ⟨x, hx, hxg⟩ :=
    T.exists_integral_root_quotient_lift_of_perfectResidue hT Q hQ a ha0 g hg
  refine ⟨x, hx, hxg.symm ▸ hg, hxg.symm ▸ hgn, ?_⟩
  intro hxn
  have hr := T.quotient_reduction_mem_rootFunctor hT Q (n • a) hna0 x hxn
  rw [map_nsmul, hxg] at hr
  exact hgn hr

/-- Choose an integral point with exact generic root membership and
higher-multiple exclusion both generically and in the actual quotient. -/
def perfectResidueIntegralRootPointOutsideMultiple
    {a : characterLattice S}
    (ha : T.characterSpecialization hT a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))
    {n : ℕ} (hn : 2 ≤ n) :
    {x : D.neutral.integralSections //
      D.neutral.integralPointMap x ∈ rootGroupPoints i a ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∈
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (T.characterSpecialization hT a)).carrier _ ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∉
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (n • T.characterSpecialization hT a)).carrier _ ∧
      D.neutral.integralPointMap x ∉ rootGroupPoints i (n • a)} :=
  ⟨Classical.choose (T.exists_integral_root_point_outside_nsmul_of_perfectResidue hT Q hQ ha hn),
    Classical.choose_spec (T.exists_integral_root_point_outside_nsmul_of_perfectResidue hT Q hQ ha hn)⟩


end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
