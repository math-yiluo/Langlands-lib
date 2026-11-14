import Langlands.BruhatTits.IntegralModels.FacetRootReductionKernel
import Langlands.BruhatTits.IntegralModels.IntegralRootPerfectLifting
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootSupport
import Langlands.BruhatTits.IntegralModels.IntegralFacetReflectionCriterion
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.BruhatTits.IntegralModels.IntegralRootDoubleComparison
import Langlands.BruhatTits.IntegralModels.UnramifiedQuotientFacetRoots
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Ordinary roots vanishing on the facet survive in the quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
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

/-- A doubled quotient-functor comparison factors the whole depth group
through strict depth and the actual doubled root group. -/
theorem affineRootGroup_subset_strict_mul_double_of_quotient_comparison
    {a : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (hlin : ψ.linear = rootForm P.i a)
    (hzero : ∀ y ∈ Fa, ψ y = 0) (hne : Fa.Nonempty)
    (hcompare : RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT.1 a.val) =
      RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (2 • T.characterSpecialization hT.1 a.val))
    (hdouble : rootGroupPoints P.i (2 • a.val) = doubleRootGroupPoints P.i a.val) :
    (P.affineRootGroup a ψ : Set (rationalPoints G)) ⊆
      (P.apartment.affineRootGroupPlus a ψ : Set (rationalPoints G)) *
        (doubleRootGroupPoints P.i a.val : Set (rationalPoints G)) := by
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  intro u hu
  have huintegral := conjugated_affineRootGroup_le_integralPoints P C e he E g Fa D
    hD hA hlin (fun y hy => (hzero y hy).ge) ⟨u, hu, rfl⟩
  obtain ⟨x, hxmap⟩ := huintegral
  have huroot := P.apartment.affineRootGroup_le_rootGroupPoints a ψ hu
  have hxroot : D.neutral.integralPointMap x ∈
      rootGroupPoints (P.i ≫ (G.innerIso g).hom) a.val := by
    rw [hxmap]
    exact RelativeRoot.comp_mem_subgroup P.i a.val (G.innerIso g).hom huroot
  have hxred := T.quotient_reduction_mem_rootFunctor hT.1 Q a.val a.property.1 x hxroot
  rw [hcompare] at hxred
  have h2a0 : 2 • a.val ≠ 0 :=
    P.isMaximalSplitTorus.1.1.nsmul_ne_zero a.property.1 (by decide)
  obtain ⟨y, hyroot, hyred⟩ :=
    T.exists_integral_root_quotient_lift_of_perfectResidue hT.1 Q hQ
      (2 • a.val) h2a0 (Q.reductiveReduction x)
      (by simpa only [map_nsmul, SpecialFibreQuotientData.reductiveReduction,
        SpecialFibreQuotientData.projectionPoints, MonoidHom.comp_apply] using hxred)
  let w := rationalPoints.map (G.innerIso g).inv (D.neutral.integralPointMap y)
  have hwmap : rationalPoints.map (G.innerIso g).hom w =
      D.neutral.integralPointMap y := by
    simp only [w, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hwroot2 : w ∈ rootGroupPoints P.i (2 • a.val) := by
    have h := RelativeRoot.comp_mem_subgroup (P.i ≫ (G.innerIso g).hom) (2 • a.val)
      (G.innerIso g).inv hyroot
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h
  have hwdouble : w ∈ doubleRootGroupPoints P.i a.val := hdouble ▸ hwroot2
  have hwroot : w ∈ P.rootGroup a :=
    RelativeRoot.double_subgroup_le P.i a.val _ hwroot2
  have hwint : rationalPoints.map (G.innerIso g).hom w ∈ D.neutral.integralPoints :=
    hwmap.symm ▸ (show D.neutral.integralPointMap y ∈ D.neutral.integralPoints from ⟨y, rfl⟩)
  have hwfixer := (conjugated_rootPoint_mem_integralPoints_iff P C e hinj he E g Fa D
    hD hA hwroot).mp hwint
  obtain ⟨y₀, hy₀⟩ := hne
  have hwdepth : w ∈ P.affineRootGroup a ψ := by
    apply (P.apartment.mem_affineRootGroup_iff hlin y₀).mpr
    refine ⟨hwroot, ?_⟩
    rw [hzero y₀ hy₀]
    exact ((P.apartment.mem_rootFixer.mp hwfixer).2 y₀ hy₀).2
  let z : D.neutral.integralSections := x * y⁻¹
  have hzmap : D.neutral.integralPointMap z =
      rationalPoints.map (G.innerIso g).hom (u * w⁻¹) := by
    dsimp only [z]
    rw [map_mul, map_inv, hxmap, ← hwmap, map_mul, map_inv]
  have hzdepth : D.neutral.integralPointMap z ∈
      (P.affineRootGroup a ψ).map (rationalPoints.map (G.innerIso g).hom) :=
    ⟨u * w⁻¹, (P.affineRootGroup a ψ).mul_mem hu
      ((P.affineRootGroup a ψ).inv_mem hwdepth), hzmap.symm⟩
  have hzone : Q.reductiveReduction z = 1 := by
    dsimp only [z]
    rw [map_mul, map_inv]
    change Q.reductiveReduction x *
      (rationalPoints.map Q.projection (D.neutral.reduction y))⁻¹ = 1
    rw [hyred, mul_inv_cancel]
  have hzstrict := (quotient_reduction_eq_one_iff_mem_strictDepth P C e hinj he E g Fa D
    hD hA hR hopp T hT Q hQ hlin hzero ⟨y₀, hy₀⟩ z hzdepth).mp hzone
  obtain ⟨v, hv, hveq⟩ := hzstrict
  refine ⟨v, hv, w, hwdouble, ?_⟩
  change v * w = u
  apply (cancel_mono (G.innerIso g).hom.hom.hom).mp
  change rationalPoints.map (G.innerIso g).hom (v * w) =
    rationalPoints.map (G.innerIso g).hom u
  rw [map_mul, hveq, hzmap, map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- The derivative of every ordinary affine root vanishing on the subset
is an actual root of the supplied reductive quotient after specialization. -/
theorem quotient_root_of_mem_facetDerivativeRoots
    (hne : Fa.Nonempty) {a : characterLattice P.S}
    (ha : a ∈ facetDerivativeRoots P.toValuationBuildingData Fa) :
    T.characterSpecialization hT.1 a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨haroot, ψ, hψ, hlin, hzero⟩ := ha
  obtain ⟨b, hb, hnot⟩ := hψ
  have hba : b = ⟨a, haroot⟩ :=
    Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split
      P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (hb.symm.trans hlin)
  subst b
  by_contra hfirst
  have ha' : a ∈ relativeRoots (P.i ≫ (G.innerIso g).hom) := by
    have h := (roots_mem_of_transport_iff (Iso.refl P.S) (G.innerIso g)
      (j := P.i ≫ (G.innerIso g).hom)
      (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp]) a).mpr haroot
    simpa only [relativeRoots, characterLattice.congr_apply, Iso.refl_inv,
      Category.id_comp] using h
  have hroot' := relativeRootSystem F G P.isConnectedReductive P.S
    (P.i ≫ (G.innerIso g).hom) (P.isMaximalSplitTorus.comp_iso (G.innerIso g))
  have : Mono (P.i ≫ (G.innerIso g).hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (P.isMaximalSplitTorus.comp_iso (G.innerIso g))
  have hcompare := T.quotient_subgroup_eq_double_of_absent_root hT.1 Q hQ
    hroot' ha' hfirst
  have hdouble := rootGroupPoints_double_eq_doubleRootGroupPoints P.i
    P.isMaximalSplitTorus.isSplitSubtorus.1
    (relativeRootSystem F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
    haroot
  exact hnot (affineRootGroup_subset_strict_mul_double_of_quotient_comparison
    P C e hinj he E g Fa D hD hA hR hopp T hT Q hQ hlin hzero hne
    (by simpa only [map_nsmul] using hcompare) hdouble)

/-- Exact character-preserving comparison of quotient roots with ordinary
facet derivatives, retaining the integral opposite-factor premise. -/
theorem quotient_root_iff_mem_facetDerivativeRoots
    (hne : Fa.Nonempty) (a : characterLattice P.S) :
    T.characterSpecialization hT.1 a ∈
        relativeRoots (T.specialFibreInclusion ≫ Q.projection) ↔
      a ∈ facetDerivativeRoots P.toValuationBuildingData Fa :=
  ⟨mem_facetDerivativeRoots_of_quotient_root P C e hinj he E g Fa D hD hA hR
      hopp T hT Q hQ hne,
    quotient_root_of_mem_facetDerivativeRoots P C e hinj he E g Fa D hD hA hR
      hopp T hT Q hQ hne⟩

/-- The same exact root comparison in the special-fibre character lattice. -/
theorem mem_quotient_roots_iff_inverse_specialization_mem_facetDerivativeRoots
    (hne : Fa.Nonempty) (χ : characterLattice T.specialFibre) :
    χ ∈ relativeRoots (T.specialFibreInclusion ≫ Q.projection) ↔
      (T.characterSpecialization hT.1).symm χ ∈
        facetDerivativeRoots P.toValuationBuildingData Fa := by
  simpa only [AddEquiv.apply_symm_apply] using
    quotient_root_iff_mem_facetDerivativeRoots P C e hinj he E g Fa D hD hA hR
      hopp T hT Q hQ hne ((T.characterSpecialization hT.1).symm χ)

/-- Canonical specialization restricts to a bijection between ordinary
facet derivatives and the actual roots of the reductive quotient. -/
def facetDerivativeRootQuotientEquiv (hne : Fa.Nonempty) :
    {a : characterLattice P.S // a ∈ facetDerivativeRoots P.toValuationBuildingData Fa} ≃
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) :=
  (T.characterSpecialization hT.1).toEquiv.subtypeEquiv (fun a =>
    (quotient_root_iff_mem_facetDerivativeRoots P C e hinj he E g Fa D hD hA hR
      hopp T hT Q hQ hne a).symm)

@[simp] theorem facetDerivativeRootQuotientEquiv_character (hne : Fa.Nonempty)
    (a : {χ : characterLattice P.S //
      χ ∈ facetDerivativeRoots P.toValuationBuildingData Fa}) :
    (facetDerivativeRootQuotientEquiv P C e hinj he E g Fa D hD hA hR hopp
      T hT Q hQ hne a).val = T.characterSpecialization hT.1 a.val := rfl

end Langlands.BruhatTits.IntegralModels
