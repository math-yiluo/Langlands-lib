import Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootPoints
import Langlands.BruhatTits.IntegralModels.StrictDepthFacetKernel
import Langlands.BruhatTits.IntegralModels.MappedOrdinaryRootQuotientCertificate

/-! # Exact root-depth kernels and ordinary facet roots -/

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
  {a : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
  (hlin : ψ.linear = rootForm P.i a)
  (hzero : ∀ y ∈ Fa, ψ y = 0)

include he hD hA hopp hT hQ hlin hzero

/-- At an exact depth jump vanishing on the subset, both actual opposite
factors are integral, so the original point is outside the radical preimage. -/
theorem conjugated_rootPoint_not_mem_positivePoints_of_mem_diff
    {x : rationalPoints G} (hx : x ∈ P.affineRootGroup a ψ)
    (hxplus : x ∉ P.apartment.affineRootGroupPlus a ψ) :
    rationalPoints.map (G.innerIso g).hom x ∉ Q.positivePoints := by
  obtain ⟨hxroot, hx1, hlevel⟩ := P.reflectionFunctional_eq_of_mem_diff hlin hx hxplus
  obtain ⟨p, hp⟩ := P.hasOppositeFactorPairs a a.property x hxroot hx1
  obtain ⟨hp1, hp2⟩ :=
    P.toValuationBuildingData.oppositeFactors_mem_neg_affineRootGroup hxroot hx1 hp hlevel
  have hneg : -a.val ∈ relativeRoots P.i := by
    rw [← hp.weylAction_eq_neg P.i P.isMaximalSplitTorus.isSplitSubtorus.1
      a.property.1 hxroot hx1]
    exact weylAction_mapsTo_relativeRoots P.i _ a.property
  have hlinneg : (-ψ).linear = rootForm P.i ⟨-a.val, hneg⟩ := by
    rw [AffineMap.neg_linear, hlin]
    apply LinearMap.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun w => ?_
    simp only [LinearMap.neg_apply, rootForm_mk, eval_neg_char]
  have hnegint := conjugated_affineRootGroup_le_integralPoints P C e he E g Fa D hD
    hA hlinneg (fun y hy => by
      change 0 ≤ -(ψ y)
      rw [hzero y hy, neg_zero])
  have hp1int : rationalPoints.map (G.innerIso g).hom p.1 ∈
      D.neutral.integralPoints := hnegint ⟨p.1, hp1, rfl⟩
  have hp2int : rationalPoints.map (G.innerIso g).hom p.2 ∈
      D.neutral.integralPoints := hnegint ⟨p.2, hp2, rfl⟩
  have hxint := conjugated_affineRootGroup_le_integralPoints P C e he E g Fa D hD hA
    hlin (fun y hy => (hzero y hy).ge) ⟨x, hx, rfl⟩
  have hpair := hp.map (G.innerIso g).hom rfl
  have hxroot' : rationalPoints.map (G.innerIso g).hom x ∈
      rootGroupPoints (P.i ≫ (G.innerIso g).hom) a.val :=
    RelativeRoot.comp_mem_subgroup P.i a.val (G.innerIso g).hom hxroot
  have ha' : a.val ∈ relativeRoots (P.i ≫ (G.innerIso g).hom) := by
    have ht := (roots_mem_of_transport_iff (Iso.refl P.S) (G.innerIso g)
      (j := P.i ≫ (G.innerIso g).hom)
      (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp]) a.val).mpr a.property
    simpa only [relativeRoots, characterLattice.congr_apply, Iso.refl_inv,
      Category.id_comp] using ht
  have hx1' : rationalPoints.map (G.innerIso g).hom x ≠ 1 := by
    intro h
    apply hx1
    apply (cancel_mono (G.innerIso g).hom.hom.hom).mp
    change rationalPoints.map (G.innerIso g).hom x =
      rationalPoints.map (G.innerIso g).hom 1
    simpa only [map_one] using h
  exact (hopp F G P.isConnectedReductive P.S (P.i ≫ (G.innerIso g).hom)
    (P.isMaximalSplitTorus.comp_iso (G.innerIso g)) D T Q hT hQ
    a.val ha' _ hxroot' hx1' hxint _ hpair.1 _ hpair.2.1 hpair.2.2).mp
      ⟨hp1int, hp2int⟩

include hinj hR in
/-- In the whole depth group of a functional vanishing on a nonempty subset,
the actual quotient-reduction kernel consists exactly of strict-depth sections. -/
theorem quotient_reduction_eq_one_iff_mem_strictDepth
    (hne : Fa.Nonempty) (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈
      (P.affineRootGroup a ψ).map (rationalPoints.map (G.innerIso g).hom)) :
    Q.reductiveReduction x = 1 ↔
      D.neutral.integralPointMap x ∈
        (P.apartment.affineRootGroupPlus a ψ).map
          (rationalPoints.map (G.innerIso g).hom) := by
  constructor
  · intro hxone
    obtain ⟨v, hv, hveq⟩ := hx
    refine ⟨v, ?_, hveq⟩
    by_contra hvplus
    apply conjugated_rootPoint_not_mem_positivePoints_of_mem_diff P C e he E g Fa D hD
      hA hopp T hT Q hQ hlin hzero hv hvplus
    rw [hveq]
    apply Subgroup.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    rw [← Q.ker_reductiveReduction hQ.2.1]
    exact hxone
  · intro hxplus
    obtain ⟨y, hy⟩ := hne
    exact strictDepthIntegralSections_le_reductiveReduction_ker P C e hinj he E g Fa D hD
      hA hR hlin hy (hzero y hy) hopp T hT Q hQ hxplus

include hinj hR in
/-- Certify the original ordinary affine root at a nonempty facet zero from
one actual quotient point outside the doubled specialized root functor. -/
def facetOrdinaryRootOfQuotientExclusion
    (hne : Fa.Nonempty) (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈
      (P.affineRootGroup a ψ).map (rationalPoints.map (G.innerIso g).hom))
    (houtside : Q.reductiveReduction x ∉
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (2 • T.characterSpecialization hT.1 a.val)).carrier _) :
    P.affineRoots := by
  apply T.ordinaryRootOfMappedQuotientExclusion P.apartment (G.innerIso g).hom hT.1 Q
    hlin
    (conjugated_affineRootGroup_le_integralPoints P C e he E g Fa D hD hA hlin
      (fun y hy => (hzero y hy).ge))
    (fun z hz => ?_) x hx houtside
  exact (quotient_reduction_eq_one_iff_mem_strictDepth P C e hinj he E g Fa D hD hA hR
    hopp T hT Q hQ hlin hzero hne z
    (Subgroup.map_mono (P.apartment.affineRootGroupPlus_le a ψ) hz)).mpr hz

@[simp] theorem facetOrdinaryRootOfQuotientExclusion_coe
    (hne : Fa.Nonempty) (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈
      (P.affineRootGroup a ψ).map (rationalPoints.map (G.innerIso g).hom))
    (houtside : Q.reductiveReduction x ∉
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (2 • T.characterSpecialization hT.1 a.val)).carrier _) :
    (facetOrdinaryRootOfQuotientExclusion P C e hinj he E g Fa D hD hA hR hopp T hT Q hQ
      hlin hzero hne x hx houtside : P.Apartment →ᵃ[ℝ] ℝ) = ψ := rfl

end Langlands.BruhatTits.IntegralModels
