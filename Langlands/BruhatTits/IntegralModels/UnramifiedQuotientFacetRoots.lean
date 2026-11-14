import Langlands.BruhatTits.IntegralModels.FacetRootReductionKernel
import Langlands.BruhatTits.IntegralModels.IntegralRootPerfectLifting
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootSupport
import Langlands.BruhatTits.IntegralModels.IntegralFacetReflectionCriterion
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction

/-! # Quotient roots give ordinary affine roots vanishing on the facet -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : P.ReducedBuilding → C.ReducedBuilding) (hinj : Function.Injective e)
  (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (g : rationalPoints G) (Fa : Set P.Apartment)
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (hD : D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      (e '' (P.translatedApartmentMap g '' Fa)))
  (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
  (hopp : IntegralOppositeFactorsStatement.{u})
  (T : IntegralTorusData D P.S (P.i ≫ (G.innerIso g).hom))
  (hT : T.IsClosedSplit) (Q : SpecialFibreQuotientData D)
  (hQ : Q.IsReductiveQuotient)

include hinj he hD hA hR hopp hT hQ

/-- Every actual quotient root is the specialization of the derivative of an
ordinary affine root vanishing on the given nonempty apartment subset. -/
theorem mem_facetDerivativeRoots_of_quotient_root
    (hne : Fa.Nonempty) {a : characterLattice P.S}
    (ha : T.characterSpecialization hT.1 a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection)) :
    a ∈ facetDerivativeRoots P.toValuationBuildingData Fa := by
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  obtain ⟨b, hb, hba⟩ := T.relativeRoots_quotient_subset_image hT.1 Q hQ ha
  have ha' : a ∈ relativeRoots (P.i ≫ (G.innerIso g).hom) := by
    have h := (T.characterSpecialization hT.1).injective hba
    exact h ▸ hb
  have haroot : a ∈ relativeRoots P.i := by
    have h := (roots_mem_of_transport_iff (Iso.refl P.S) (G.innerIso g)
      (j := P.i ≫ (G.innerIso g).hom)
      (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp]) a).mp
    apply h
    simpa only [relativeRoots, characterLattice.congr_apply, Iso.refl_inv,
      Category.id_comp] using ha'
  let α : relativeRoots P.i := ⟨a, haroot⟩
  obtain ⟨x, hxroot, _, hxout, hxoutgen⟩ :=
    T.exists_integral_root_point_outside_nsmul_of_perfectResidue hT.1 Q hQ ha
      (show 2 ≤ (2 : ℕ) by rfl)
  let u := rationalPoints.map (G.innerIso g).inv (D.neutral.integralPointMap x)
  have hueq : rationalPoints.map (G.innerIso g).hom u =
      D.neutral.integralPointMap x := by
    simp only [u, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have huroot : u ∈ P.rootGroup α := by
    have h := RelativeRoot.comp_mem_subgroup (P.i ≫ (G.innerIso g).hom) a
      (G.innerIso g).inv hxroot
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    apply hxoutgen
    rw [← hueq, h, map_one]
    exact (rootGroupPoints (P.i ≫ (G.innerIso g).hom) (2 • a)).one_mem
  have huint : rationalPoints.map (G.innerIso g).hom u ∈ D.neutral.integralPoints :=
    hueq.symm ▸ (show D.neutral.integralPointMap x ∈ D.neutral.integralPoints from ⟨x, rfl⟩)
  have hunotpos : rationalPoints.map (G.innerIso g).hom u ∉ Q.positivePoints := by
    intro h
    rw [hueq] at h
    obtain ⟨y, hy, hyx⟩ := h
    have hxy : y = x := D.neutral.integralPointMap_injective hyx
    subst y
    have hxone : Q.reductiveReduction x = 1 := by
      rw [← MonoidHom.mem_ker, Q.ker_reductiveReduction hQ.2.1]
      exact hy
    apply hxout
    change Q.reductiveReduction x ∈ _
    rw [hxone]
    exact ((RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (2 • T.characterSpecialization hT.1 a)).carrier _).one_mem
  obtain ⟨p, hp⟩ := P.hasOppositeFactorPairs α α.property u huroot hu1
  have hp' := hp.map (G.innerIso g).hom rfl
  have hu1' : rationalPoints.map (G.innerIso g).hom u ≠ 1 := by
    intro h
    apply hu1
    apply (cancel_mono (G.innerIso g).hom.hom.hom).mp
    change rationalPoints.map (G.innerIso g).hom u =
      rationalPoints.map (G.innerIso g).hom 1
    simpa only [map_one] using h
  have hpint := (hopp F G P.isConnectedReductive P.S (P.i ≫ (G.innerIso g).hom)
    (P.isMaximalSplitTorus.comp_iso (G.innerIso g)) D T Q hT hQ
    a ha' _ (hueq.symm ▸ hxroot) hu1' huint _ hp'.1 _ hp'.2.1 hp'.2.2).mpr hunotpos
  have hrefint : rationalPoints.map (G.innerIso g).hom (P.reflectionElement hp) ∈
      D.neutral.integralPoints := by
    rw [ValuationBuildingData.coe_reflectionElement, map_mul, map_mul]
    exact D.neutral.integralPoints.mul_mem
      (D.neutral.integralPoints.mul_mem hpint.1 huint) hpint.2
  have hzero := (conjugated_reflection_mem_integralPoints_iff P C e hinj he E g Fa D
    hD hA hR huroot hu1 hp).mp hrefint
  have hdepth : u ∈ P.affineRootGroup α (P.reflectionFunctional α u) := by
    obtain ⟨y, _⟩ := hne
    exact (P.apartment.mem_affineRootGroup_iff (P.reflectionFunctional_linear α u) y).mpr
      ⟨huroot, (P.coe_reflectionFunctional_apply huroot hu1 y).le⟩
  have hxdepth : D.neutral.integralPointMap x ∈
      (P.affineRootGroup α (P.reflectionFunctional α u)).map
        (rationalPoints.map (G.innerIso g).hom) := ⟨u, hdepth, hueq⟩
  have hord := (facetOrdinaryRootOfQuotientExclusion P C e hinj he E g Fa D hD hA hR
    hopp T hT Q hQ (P.reflectionFunctional_linear α u) hzero hne x hxdepth hxout).property
  exact ⟨haroot, P.reflectionFunctional α u, hord,
    P.reflectionFunctional_linear α u, hzero⟩

/-- The quotient-root character transported back to the actual derivative-root
set, with no change of character or root length. -/
def facetDerivativeRootOfQuotientRoot (hne : Fa.Nonempty)
    (a : relativeRoots (T.specialFibreInclusion ≫ Q.projection)) :
    {χ : characterLattice P.S // χ ∈ facetDerivativeRoots P.toValuationBuildingData Fa} :=
  ⟨(T.characterSpecialization hT.1).symm a.val,
    mem_facetDerivativeRoots_of_quotient_root P C e hinj he E g Fa D hD hA hR hopp
      T hT Q hQ hne (by simpa only [AddEquiv.apply_symm_apply] using a.property)⟩

@[simp] theorem facetDerivativeRootOfQuotientRoot_character (hne : Fa.Nonempty)
    (a : relativeRoots (T.specialFibreInclusion ≫ Q.projection)) :
    (facetDerivativeRootOfQuotientRoot P C e hinj he E g Fa D hD hA hR hopp
      T hT Q hQ hne a).val = (T.characterSpecialization hT.1).symm a.val := rfl

end Langlands.BruhatTits.IntegralModels
