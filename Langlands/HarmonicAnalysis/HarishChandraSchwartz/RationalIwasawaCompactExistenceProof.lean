import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalIwasawaCompactExistence
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof
import Langlands.Geometry.Building.IntegerValuationLocalComparison
import Langlands.Geometry.Building.IntegerValuationOneStabilizerBounded
import Langlands.Geometry.Building.CentralizerNormKernelConstruction
import Langlands.Geometry.Building.ValuationBuildingTopologyCompatible
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.GroupScheme.Rational.OpenRootGenerationProof
import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel
import Langlands.Geometry.Building.SpecialPointFixedLocus
import Langlands.Geometry.Building.IwasawaDecompositionReduction
import Langlands.GroupScheme.Rational.RootAnnihilatorRank
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof

/-! # Compact open Iwasawa existence on rational points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable
open Langlands.Geometry.Building Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

set_option maxHeartbeats 1600000 in
private theorem nonempty_valuationBuildingData (hG : IsConnectedReductive G) :
    Nonempty (ValuationBuildingData G) := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨S, iS, hiS⟩ := exists_maximalSplitTorus G
  obtain ⟨T, iT, f, hf, -, hiT⟩ := specialTorusExistence F G hG S iS hiS
  have := mono_of_isMaximalSplitTorus hiS
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  have hqs : IsQuasiSplit (baseChanged F (inertiaFixedField F) G) :=
    unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit F _ hGK
  obtain ⟨D, C, h6⟩ := quasiSplitIntegerApartmentExistence (inertiaFixedField F)
    (MaximalUnramified.valuation F) (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F)
    (baseChanged F (inertiaFixedField F) G) hqs
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) hiT
  have hE : RelativeRoot.HasOppositeFactorPairs
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _
      hiT.isSplitSubtorus.1).mp
      (rootRankOneFactorization (inertiaFixedField F) (baseChanged F (inertiaFixedField F) G)
        hGK _ _ hiT)
  obtain ⟨DS, CS, h6S, -, -, -⟩ := unramifiedValuationDescent F G hG S iS hiS T iT f hf
    hiT hE D C h6
  exact ⟨⟨hG, S, iS, hiS, DS, CS, h6S⟩⟩

variable (B : ValuationBuildingData G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance rationalIwasawaCompactExistenceProofTopologicalSpace : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

private theorem filtration_le_compactStabilizer (x : B.Apartment) (a : relativeRoots B.i) :
    B.filtration x a 0 ≤ B.compactStabilizer (B.apartmentMap x) := by
  apply le_trans _ (B.sharpFixer_le_compactStabilizer B.isTopologyCompatible (Set.mem_singleton x))
  change B.apartment.filtration x a 0 ≤ B.apartment.sharpFixer {x}
  rw [← B.apartment.rootFixer_singleton]
  exact B.apartment.rootFixer_le_sharpFixer a {x}

private theorem isOpen_compactStabilizer (x : B.Apartment) :
    IsOpen (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hopen := RelativeRoot.openRootCentralizerGeneration F G B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus B.centralizer.Z B.centralizer.j B.centralizer.isRepresentedBy
    B.centralizer.isClosedSubgroup (fun a => B.filtration x a 0)
    (rationalCommonNormKernel B.centralizer.Z) (fun a => B.filtration_le_rootGroup x a 0)
    (fun a => (B.filtrationOpenSubgroup B.isTopologyCompatible x a 0).isOpen')
    B.isOpen_centralizerNormKernel
  apply Subgroup.isOpen_mono _ hopen
  apply sup_le _ (iSup_le fun a => filtration_le_compactStabilizer B x a)
  rintro _ ⟨z, hz, rfl⟩
  exact B.map_mem_compactStabilizer hz x

private theorem isCompact_compactStabilizer (x : B.Apartment) :
    IsCompact (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let C := IntegerValuationBuildingData.ofLocal B
  have hZ : IsAlgebraicallyBounded F G.X (rationalPoints.map C.centralizer.j ''
      (characterValuationKernel (FML.normalizedMultiplicativeValuation F) C.centralizer.Z :
        Set (rationalPoints C.centralizer.Z))) := by
    rw [IntegerValuation.characterValuationKernel_normalized]
    exact B.isAlgebraicallyBounded_image_centralizerNormKernel
  have hU (y : C.Apartment) (a : characterLattice C.S) (ha : a ∈ relativeRoots C.i) :
      IsAlgebraicallyBounded F G.X (C.filtration y a 0 : Set (rationalPoints G)) := by
    obtain ⟨y, rfl⟩ := (IntegerValuationBuildingData.ofLocalApartmentEquiv B).surjective y
    rw [IntegerValuationBuildingData.ofLocal_filtration]
    exact ((B.isTopologyCompatible y.val y.mem a ha).2 0).2
  have hb := C.isAlgebraicallyBounded_oneStabilizer hZ hU
    (IntegerValuationBuildingData.ofLocalBuildingEquiv B (B.apartmentMap x))
  rw [IntegerValuationBuildingData.ofLocal_oneStabilizer] at hb
  let K : OpenSubgroup (rationalPoints G) :=
    ⟨B.compactStabilizer (B.apartmentMap x), isOpen_compactStabilizer B x⟩
  have hc : IsClosed (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G)) :=
    K.isClosed
  simpa only [hc.closure_eq] using hb.isCompact_closure G.X

local instance : Mono B.i.hom.hom.left := B.isMaximalSplitTorus.isSplitSubtorus.mono

set_option maxHeartbeats 2400000 in
private theorem exists_point_with_simple_reflection_lifts (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) :
    ∃ x : B.Apartment, ∀ a ∈ simpleRelativeRoots B.i ν,
      ∃ n : normalizerPoints B.i,
        IsRelativeReflection B.i a (QuotientGroup.mk n) ∧
          (n : rationalPoints G) ∈ B.compactStabilizer (B.apartmentMap x) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hS := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hR := relativeRootSystem F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hsub := (simpleRelativeRoots_subset_positive B.i ν).trans
    (positiveRelativeRoots_subset_relativeRoots B.i ν)
  have : Finite (simpleRelativeRoots B.i ν) := (hR.finite_simpleRelativeRoots B.i hS ν).to_subtype
  let x₀ : B.Apartment := Classical.arbitrary _
  have hfin (a : simpleRelativeRoots B.i ν) :
      ∃ g ∈ B.rootGroup a, ∃ t : ℝ, x₀.val a g = (t : WithTop ℝ) := by
    obtain ⟨g, hg, hgt⟩ := x₀.isValuation.exists_ne_top (hsub a.2)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hgt
    exact ⟨g, hg, t, ht.symm⟩
  choose g hg t ht using hfin
  obtain ⟨w, hw⟩ := rootEvaluation_surjective hS (simpleRelativeRoots B.i ν)
    (hR.linearIndependent_simpleRelativeRoots B.i ν hS hν) (fun a => -t a)
  let x : B.Apartment := (Submodule.Quotient.mk w : TranslationSpace B.i) +ᵥ x₀
  refine ⟨x, fun a ha => ?_⟩
  let b : simpleRelativeRoots B.i ν := ⟨a, ha⟩
  let α : relativeRoots B.i := ⟨a, hsub ha⟩
  have hg1 : g b ≠ 1 := by
    intro h
    have htop := (x₀.isValuation.eq_top_iff a α.2 (g b) (hg b)).2 h
    rw [ht b] at htop
    exact WithTop.coe_ne_top htop
  have hval : x.val a (g b) = 0 := by
    have he := congrFun hw b
    change eval B.S a w = -t b at he
    change ((Submodule.Quotient.mk w : TranslationSpace B.i) +ᵥ x₀).val a (g b) = 0
    rw [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply, he, ht b,
      ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
  have hRank := rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  obtain ⟨⟨p, hp, -⟩, hprop⟩ := hRank a α.2 (g b) (hg b) hg1
  obtain ⟨-, -, hrefl, -⟩ := hprop p hp
  let n := B.reflectionElement (α := α) hp
  have hfix : n • x = x :=
    RootReflectionProof.hasRootReflections B α (g b) (hg b) hg1 p hp x hval
  have hnorm : (n : rationalPoints G) ∈ rationalCommonNormKernel G :=
    B.reflectionElement_mem_rationalCommonNormKernel B.isTopologyCompatible
      (a := α) (hg b) hg1 hp
  refine ⟨n, hrefl, B.mem_compactStabilizer.mpr ⟨hnorm, ?_⟩⟩
  rw [B.normalizer_smul_apartmentMap, hfix]

/-- Below depth zero, the right opposite factor belongs to the opposite depth-zero group. -/
private theorem right_oppositeFactor_mem_filtration (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    {u : rationalPoints G} (hu : u ∈ B.rootGroup a) (huf : u ∉ B.filtration x a 0)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B.i a u p) : p.2 ∈ B.filtration x (-a) 0 := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hu1 : u ≠ 1 := fun h => huf (h ▸ (B.filtration x a 0).one_mem)
  have hneg : ¬ ((0 : ℝ) : WithTop ℝ) ≤ x.val a u :=
    fun h => huf (B.apartment.mem_filtration.mpr ⟨hu, h⟩)
  have hp₁ : p.1 ∈ B.rootGroup (-a) := hp.1
  have hp₂ : p.2 ∈ B.rootGroup (-a) := hp.2.1
  have hminv : p.2⁻¹ * u⁻¹ * p.1⁻¹ ∈ normalizerPoints B.i := by
    simpa only [mul_inv_rev, mul_assoc] using (normalizerPoints B.i).inv_mem hp.2.2
  have hV5 := x.isValuation.opposite a ha u⁻¹ ((B.rootGroup a).inv_mem hu) (inv_ne_one.mpr hu1)
    p.2⁻¹ ((B.rootGroup (-a)).inv_mem hp₂) p.1⁻¹ ((B.rootGroup (-a)).inv_mem hp₁) hminv
  rw [RootReflectionProof.apply_inv x.isValuation (-a) p.2,
    RootReflectionProof.apply_inv x.isValuation a u] at hV5
  have hufin : x.val a u ≠ ⊤ := fun h => hneg (h ▸ le_top)
  have hpfin : x.val (-a) p.2 ≠ ⊤ := by
    intro h
    rw [h, WithTop.top_add] at hV5
    exact WithTop.top_ne_zero hV5
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hufin
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hpfin
  rw [← hv, ← ht, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at hV5
  rw [← ht, WithTop.coe_le_coe] at hneg
  refine B.apartment.mem_filtration.mpr ⟨hp₂, ?_⟩
  rw [← hv, WithTop.coe_le_coe]
  linarith [lt_of_not_ge hneg]

set_option maxHeartbeats 2400000 in
private theorem isIwasawaPair_of_simple_reflection_lifts (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) (x : B.Apartment)
    (hx : ∀ a ∈ simpleRelativeRoots B.i ν, ∃ n : normalizerPoints B.i,
      IsRelativeReflection B.i a (QuotientGroup.mk n) ∧
        (n : rationalPoints G) ∈ B.compactStabilizer (B.apartmentMap x)) :
    IsIwasawaPair (standardParabolicPoints B.i ν ∅) (B.compactStabilizer (B.apartmentMap x)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let P := standardParabolicPoints B.i ν ∅
  let K := B.compactStabilizer (B.apartmentMap x)
  let π := QuotientGroup.mk' ((centralizerPoints B.i).subgroupOf (normalizerPoints B.i))
  let X : Set (rationalPoints G) := {g | ∃ p ∈ P, ∃ k ∈ K, g = p * k}
  have hS := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hTits := (relativeTitsSystem F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus ν hν).isTitsSystem
  have hR := relativeRootSystem F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hRank := rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hF := hasSimpleRootParabolicFactorization_of_statements relativeRootSystem
    standardParabolicEndpoints genericCentralizer RelativeRoot.dynamicRootOrderedProduct
    F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus ν hν
  have hleft : ∀ b ∈ P, ∀ g ∈ X, b * g ∈ X := by
    rintro b hb g ⟨p, hp, k, hk, rfl⟩
    exact ⟨b * p, P.mul_mem hb hp, k, hk, (mul_assoc b p k).symm⟩
  have hright : ∀ g ∈ X, ∀ k ∈ K, g * k ∈ X := by
    rintro g ⟨p, hp, k₀, hk₀, rfl⟩ k hk
    exact ⟨p, hp, k₀ * k, K.mul_mem hk₀ hk, mul_assoc p k₀ k⟩
  have hcompare (n j : normalizerPoints B.i) (h : π n = π j) :
      (n : rationalPoints G) * (j : rationalPoints G)⁻¹ ∈ P := by
    have hker : n * j⁻¹ ∈ π.ker := by
      change π (n * j⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    change n * j⁻¹ ∈ (QuotientGroup.mk'
      ((centralizerPoints B.i).subgroupOf (normalizerPoints B.i))).ker at hker
    rw [hTits.ker_eq, Subgroup.mem_subgroupOf] at hker
    exact hker
  intro g
  change g ∈ X
  refine hTits.mem_of_stable (X := X) ⟨1, P.one_mem, 1, K.one_mem, (one_mul 1).symm⟩ hleft ?_ g
  intro s hs n hn g' hg'
  obtain ⟨b, hb, k, hk, rfl⟩ := hg'
  obtain ⟨a, ha, has⟩ := hs
  obtain ⟨j, hj, hjK⟩ := hx a ha
  have hjπ : π j = s := hR.eq_of_isRelativeReflection hj has
  have hnP := hcompare n j (hn.trans hjπ.symm)
  obtain ⟨b', hb', u, hu, rfl⟩ := hF a ha s has b hb
  have hb'P := hb' j hjπ
  let e := (j : rationalPoints G) * u * (j : rationalPoints G)⁻¹
  have heRoot : e ∈ B.rootGroup (-a) := by
    have hconj := conj_mem_rootGroupPoints j (a := a) hu
    rwa [IsRelativeReflection.weylAction_apply_self B.i hS j hj] at hconj
  have hna := IsRelativeReflection.neg_mem_relativeRoots B.i has hS
  have heX : e ∈ X := by
    by_cases he0 : e ∈ B.filtration x (-a) 0
    · exact ⟨1, P.one_mem, e, filtration_le_compactStabilizer B x ⟨-a, hna⟩ he0,
        (one_mul e).symm⟩
    have he1 : e ≠ 1 := fun h => he0 (h ▸ (B.filtration x (-a) 0).one_mem)
    obtain ⟨⟨p, hp, -⟩, hprop⟩ := hRank (-a) hna e heRoot he1
    obtain ⟨-, -, hm, -⟩ := hprop p hp
    let m : normalizerPoints B.i := ⟨p.1 * e * p.2, hp.2.2⟩
    have hmπ : π m = s := hR.eq_of_isRelativeReflection (hm.of_neg has.mem_relativeRoots) has
    have hmP := hcompare m j (hmπ.trans hjπ.symm)
    have hp₁ : p.1 ∈ B.rootGroup a := by
      have hp₁ : p.1 ∈ B.rootGroup (-(-a)) := hp.1
      simpa only [neg_neg] using hp₁
    have hp₁P : p.1 ∈ P := RelativeRoot.subgroup_le_standardParabolic_empty B.i ν ha _ hp₁
    have hp₂ : p.2 ∈ B.filtration x a 0 := by
      simpa only [neg_neg] using right_oppositeFactor_mem_filtration B x hna heRoot he0 hp
    have hp₂K : p.2 ∈ K :=
      filtration_le_compactStabilizer B x ⟨a, has.mem_relativeRoots⟩ hp₂
    refine ⟨p.1⁻¹ * ((m : rationalPoints G) * (j : rationalPoints G)⁻¹),
      P.mul_mem (P.inv_mem hp₁P) hmP, (j : rationalPoints G) * p.2⁻¹,
      K.mul_mem hjK (K.inv_mem hp₂K), ?_⟩
    change e = (p.1⁻¹ * ((p.1 * e * p.2) * (j : rationalPoints G)⁻¹)) *
      ((j : rationalPoints G) * p.2⁻¹)
    group
  have hk' := hright e heX ((j : rationalPoints G) * k) (K.mul_mem hjK hk)
  have h := hleft _ hnP _ (hleft _ hb'P _ hk')
  convert h using 1
  dsimp only [e]
  group

omit [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom] in
/-- A compact open Iwasawa subgroup on the actual rational points. -/
theorem rationalIwasawaCompactExistence : RationalIwasawaCompactExistenceStatement.{u} := by
  intro F _ _ _ _ G _ _ hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨B⟩ := nonempty_valuationBuildingData hG
  obtain ⟨ν, hν⟩ := B.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B.i
  obtain ⟨x, hx⟩ := exists_point_with_simple_reflection_lifts B ν hν
  let K : OpenSubgroup (rationalPoints G) :=
    ⟨B.compactStabilizer (B.apartmentMap x), isOpen_compactStabilizer B x⟩
  exact ⟨B.S, B.i, ν, K, B.isMaximalSplitTorus, hν, isCompact_compactStabilizer B x,
    isIwasawaPair_of_simple_reflection_lifts B ν hν x hx⟩

end Langlands.HarishChandraSchwartz
