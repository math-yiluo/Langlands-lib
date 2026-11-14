import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.GroupScheme.IntegralModel.SplitRootReduction

/-! # Canonical root containment after integral reduction and quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)

local instance : Smooth D.neutral.group.X.hom := D.neutral_smooth

include hT in
/-- Every integral generic-root section reduces into the root functor for
the canonical character specialization through the same integral torus. -/
theorem reduction_mem_rootFunctor (a : characterLattice S) (ha : a ≠ 0)
    (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈ rootGroupPoints i a) :
    D.neutral.reduction x ∈
      (RelativeRoot.subgroup T.specialFibreInclusion
        (T.characterSpecialization hT a)).carrier _ := by
  let χ := (T.genericCharacterEquiv hT).symm a
  have hχa : T.genericCharacter χ = a :=
    (T.genericCharacterEquiv hT).apply_symm_apply a
  have hχ : χ ≠ 0 := by
    intro hz
    apply ha
    rw [hz, map_zero] at hχa
    exact hχa.symm
  have hgen : RelativeRoot.subgroup (D.neutral.genericHom T.inclusion)
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ) =
        RelativeRoot.subgroup i a := by
    let e := CommGroupScheme.isoOfGroupIso
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus)
      (U := S) T.genericIso
    have hc : D.neutral.genericHom T.inclusion =
        CommGroupScheme.groupHom e.hom ≫ i := T.generic_comm
    have ht := RelativeRoot.subgroup_comap_of_transport e (Iso.refl G)
      (i := D.neutral.genericHom T.inclusion) (j := i)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hc)
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)
    have hchar : characterLattice.congr e
        (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ) = a := hχa
    simpa only [hchar, Iso.refl_hom, SubgroupFunctor.comap_id] using ht.symm
  have hx' : D.neutral.integralPointMap x ∈
      (RelativeRoot.subgroup (D.neutral.genericHom T.inclusion)
        (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)).carrier _ := by
    rw [hgen]
    exact hx
  have hr := IntegralModel.SplitRoot.reduction_mem_of_generic_mem
    D.neutral hT T.inclusion χ hχ x hx'
  have hs : T.characterSpecialization hT a = T.specialCharacter χ := by
    rw [← hχa, T.characterSpecialization_genericCharacter hT χ]
  rw [hs]
  exact hr

include hT in
/-- Any actual special-fibre quotient map carries the reduction of an
integral generic-root section into the corresponding quotient root functor. -/
theorem quotient_reduction_mem_rootFunctor (Q : SpecialFibreQuotientData D)
    (a : characterLattice S) (ha : a ≠ 0) (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈ rootGroupPoints i a) :
    rationalPoints.map Q.projection (D.neutral.reduction x) ∈
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT a)).carrier _ :=
  RelativeRoot.comp_mem_subgroup T.specialFibreInclusion
    (T.characterSpecialization hT a) Q.projection
    (T.reduction_mem_rootFunctor hT a ha x hx)

/-- Reduction followed by the actual quotient projection, restricted to
all integral sections whose generic point lies in the original root group. -/
def quotientRootReduction (Q : SpecialFibreQuotientData D)
    (a : characterLattice S) (ha : a ≠ 0) :
    (rootGroupPoints i a).comap D.neutral.integralPointMap →*
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT a)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))) where
  toFun x := ⟨rationalPoints.map Q.projection (D.neutral.reduction x),
    T.quotient_reduction_mem_rootFunctor hT Q a ha x x.property⟩
  map_one' := Subtype.ext (by simp only [OneMemClass.coe_one, map_one])
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])

@[simp] theorem quotientRootReduction_coe (Q : SpecialFibreQuotientData D)
    (a : characterLattice S) (ha : a ≠ 0)
    (x : (rootGroupPoints i a).comap D.neutral.integralPointMap) :
    (T.quotientRootReduction hT Q a ha x : rationalPoints Q.quotient) =
      rationalPoints.map Q.projection (D.neutral.reduction x) := rfl

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
