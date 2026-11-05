import Langlands.Geometry.Building.ChamberRankOne
import Langlands.Geometry.Building.RootReflectionAction
import Langlands.Geometry.Building.RootReflectionProof
import Langlands.Geometry.Building.NormalizerNormOneFixerBoundedness
import Langlands.Geometry.Building.KPMinimalLeviZeroStatement

/-! # Rank-one exchange with the actual centralizer-zero factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Plancherel

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

set_option maxHeartbeats 800000 in
/-- Positive total depth gives a rank-one exchange with a factor in the supplied
actual centralizer-zero subgroup, under the explicit cover comparison and pair
existence. The root factors retain the input valuation lower bounds. -/
theorem exists_rankOne_factorization_centralizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (x : P.Apartment) {α : relativeRoots P.i}
    {v v' : rationalPoints G}
    (hv : v ∈ P.rootGroup α) (hv1 : v ≠ 1)
    (hv' : v' ∈ P.rootGroup (-α.val)) (hv'1 : v' ≠ 1)
    {t t' : ℝ} (ht : x.val α v = t) (ht' : x.val (-α.val) v' = t')
    (hpos : 0 < t + t') :
    ∃ x' ∈ P.rootGroup (-α.val), ∃ z ∈ P.centralizerZero,
      ∃ y ∈ P.rootGroup α,
        v * v' = x' * rationalPoints.map P.centralizer.j z * y ∧
          (t' : WithTop ℝ) ≤ x.val (-α.val) x' ∧
          (t : WithTop ℝ) ≤ x.val α y := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let B := P.toValuationBuildingData
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hneg := KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hF x α.property
  let β : relativeRoots P.i := ⟨-α.val, hneg⟩
  have h := x.isValuation
  obtain ⟨p, hp⟩ := (hF β β.property v' hv' hv'1).1.exists
  have hp1 : p.1 ∈ P.rootGroup α := by
    have hp1' : p.1 ∈ rootGroupPoints P.i (-(-α.val)) := hp.1
    rwa [neg_neg] at hp1'
  have hp2 : p.2 ∈ P.rootGroup α := by
    have hp2' : p.2 ∈ rootGroupPoints P.i (-(-α.val)) := hp.2.1
    rwa [neg_neg] at hp2'
  have hp1t : x.val α p.1 = ((-t' : ℝ) : WithTop ℝ) := by
    have h5 := h.opposite β β.property v' hv' hv'1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    change x.val (-(-α.val)) p.1 + x.val (-α.val) v' = 0 at h5
    rw [neg_neg, ht'] at h5
    exact withTop_eq_neg_of_add_eq_zero h5
  have hp1i : x.val α p.1⁻¹ = ((-t' : ℝ) : WithTop ℝ) := by
    rw [h.apply_inv]
    exact hp1t
  have hlt : x.val α p.1⁻¹ < x.val α v := by
    rw [hp1i, ht, WithTop.coe_lt_coe]
    linarith
  have hw : v * p.1⁻¹ ∈ P.rootGroup α :=
    (P.rootGroup α).mul_mem hv ((P.rootGroup α).inv_mem hp1)
  have hwt : x.val α (v * p.1⁻¹) = ((-t' : ℝ) : WithTop ℝ) := by
    rw [h.apply_mul_eq_right_of_lt α.property hv ((P.rootGroup α).inv_mem hp1) hlt, hp1i]
  have hw1 : v * p.1⁻¹ ≠ 1 := by
    intro h1
    rw [h1, B.val_apply_one] at hwt
    exact WithTop.top_ne_coe hwt
  obtain ⟨q, hq⟩ := (hF α α.property (v * p.1⁻¹) hw hw1).1.exists
  have hq1t : x.val (-α.val) q.1 = (t' : WithTop ℝ) := by
    have h5 := h.opposite α α.property _ hw hw1 q.1 hq.1 q.2 hq.2.1 hq.2.2
    rw [hwt] at h5
    simpa only [neg_neg] using withTop_eq_neg_of_add_eq_zero h5
  let m : normalizerPoints P.i := B.reflectionElement (α := β) hp
  let n : normalizerPoints P.i := B.reflectionElement hq
  have hmflip : weylAction P.i m β = -β.val :=
    hp.weylAction_eq_neg P.i hT β.property.1 hv' hv'1
  have hminv : weylAction P.i m⁻¹ (-α.val) = α.val := by
    have h0 := weylAction_inv_apply_apply m (-α.val)
    have hmflip' : weylAction P.i m (-α.val) = α.val := by
      simpa only [β, neg_neg] using hmflip
    rw [hmflip'] at h0
    rw [map_neg, h0, neg_neg]
  have hspan := relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hZweyl := KPApartmentData.weylAction_mul_factorPairs_eq_one hT
    (hT.finite_relativeRoots P.i) hspan α.property hw hw1 hv' hv'1 hp hq
  have hzC : (n * m : normalizerPoints P.i).val ∈ centralizerPoints P.i :=
    (hT.weylAction_eq_one_iff P.i _).1 hZweyl
  have hy : m.val⁻¹ * q.2⁻¹ * m.val * p.2⁻¹ ∈ P.rootGroup α := by
    refine (P.rootGroup α).mul_mem ?_ ((P.rootGroup α).inv_mem hp2)
    have hc := conj_mem_rootGroupPoints m⁻¹
      ((P.rootGroup (-α.val)).inv_mem hq.2.1)
    rw [hminv] at hc
    simpa only [Subgroup.coe_inv, inv_inv] using hc
  have hx' : q.1⁻¹ ∈ P.rootGroup (-α.val) :=
    (P.rootGroup (-α.val)).inv_mem hq.1
  have heq : v * v' = q.1⁻¹ * (n * m : normalizerPoints P.i).val *
      (m.val⁻¹ * q.2⁻¹ * m.val * p.2⁻¹) := by
    rw [Subgroup.coe_mul]
    dsimp only [m, n, ValuationBuildingData.reflectionElement]
    group
  have hyt : (t : WithTop ℝ) ≤
      x.val α (m.val⁻¹ * q.2⁻¹ * m.val * p.2⁻¹) :=
    KPApartmentData.le_val_of_mul_eq hT hF x α.property hneg
      hv hv1 hv' hx' hzC hy heq ht ht'.ge hpos
  have hlevel : B.reflectionFunctional α (v * p.1⁻¹) =
      -B.reflectionFunctional β v' := by
    apply AffineMap.ext_linear (p := x)
    · apply LinearMap.ext
      intro w
      change rootForm P.i α w = -rootForm P.i β w
      refine Submodule.Quotient.induction_on _ w fun w0 => ?_
      simp only [rootForm_mk, β, eval_neg_char, neg_neg]
    · have hpval : B.reflectionFunctional β v' x = t' :=
        WithTop.coe_injective
          ((B.coe_reflectionFunctional_apply (α := β) hv' hv'1 x).trans ht')
      have hqval : B.reflectionFunctional α (v * p.1⁻¹) x = -t' :=
        WithTop.coe_injective
          ((B.coe_reflectionFunctional_apply (α := α) hw hw1 x).trans hwt)
      change B.reflectionFunctional α (v * p.1⁻¹) x = -B.reflectionFunctional β v' x
      rw [hpval, hqval]
  have hne : (B.reflectionFunctional β v').linear ≠ 0 := by
    intro h0
    have h2 := B.rootForm_reflectionCoroot (α := β) hv' hv'1 hp
    change (B.reflectionFunctional β v').linear _ = 2 at h2
    rw [h0, LinearMap.zero_apply] at h2
    norm_num at h2
  obtain ⟨x0, hx0⟩ := AffineRootSystem.exists_apply_eq_zero hne
  have hmfix : m • x0 = x0 := by
    apply RootReflectionProof.hasRootReflections B β v' hv' hv'1 p hp x0
    rw [B.reflectionHyperplane_eq (α := β) hv' hv'1]
    exact hx0
  have hnfix : n • x0 = x0 := by
    apply RootReflectionProof.hasRootReflections B α _ hw hw1 q hq x0
    rw [B.reflectionHyperplane_eq (α := α) hw hw1]
    change B.reflectionFunctional α (v * p.1⁻¹) x0 = 0
    rw [hlevel]
    change -B.reflectionFunctional β v' x0 = 0
    rw [hx0, neg_zero]
  have hzsc : (n * m : normalizerPoints P.i).val ∈ P.simplyConnectedImage :=
    P.simplyConnectedImage.mul_mem
      (P.reflectionElement_mem_simplyConnectedImage (α := α) hA hw hw1 hq)
      (P.reflectionElement_mem_simplyConnectedImage (α := β) hA hv' hv'1 hp)
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hzC
  obtain ⟨z, hjz⟩ : ∃ z : rationalPoints P.centralizer.Z,
      rationalPoints.map P.centralizer.j z = (n * m : normalizerPoints P.i).val := by
    obtain ⟨z, hz⟩ := hzC
    exact ⟨z, hz⟩
  have hzn : P.centralizer.toNormalizer z = n * m := Subtype.ext hjz
  have hzsc' : rationalPoints.map P.centralizer.j z ∈ P.simplyConnectedImage := by
    rwa [hjz]
  have hnorm : z ∈ rationalCommonNormKernel P.centralizer.Z := by
    refine B.mem_rationalCommonNormKernel_of_smul_eq z
      (P.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel
        (P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hzsc')) (x := x0) ?_
    rw [hzn, mul_smul, hmfix, hnfix]
  refine ⟨q.1⁻¹, hx', z, hZ ⟨hzsc', hnorm⟩, _, hy, ?_, ?_, hyt⟩
  · rwa [hjz]
  · rw [h.apply_inv, hq1t]

/-- A rank-one exchange in the actual centralizer-zero subgroup, together with
the two valuation lower bounds needed for filtered root groups. -/
structure RankOneZeroFactorizationData (x : P.Apartment)
    (α : relativeRoots P.i) (v v' : rationalPoints G) (t t' : ℝ) where
  negative : P.rootGroup (-α.val)
  central : P.centralizerZero
  positive : P.rootGroup α
  product_eq : v * v' =
    negative.val * rationalPoints.map P.centralizer.j central.val * positive.val
  negative_depth : (t' : WithTop ℝ) ≤ x.val (-α.val) negative.val
  positive_depth : (t : WithTop ℝ) ≤ x.val α positive.val

/-- Choose an actual centralizer-zero rank-one exchange at positive total depth. -/
def rankOneZeroFactorization
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (x : P.Apartment) {α : relativeRoots P.i}
    {v v' : rationalPoints G}
    (hv : v ∈ P.rootGroup α) (hv1 : v ≠ 1)
    (hv' : v' ∈ P.rootGroup (-α.val)) (hv'1 : v' ≠ 1)
    {t t' : ℝ} (ht : x.val α v = t) (ht' : x.val (-α.val) v' = t')
    (hpos : 0 < t + t') :
    P.RankOneZeroFactorizationData x α v v' t t' :=
  Classical.choice (by
    obtain ⟨a, ha, z, hz, b, hb, heq, hat, hbt⟩ :=
      P.exists_rankOne_factorization_centralizerZero hA hZ hF x
        hv hv1 hv' hv'1 ht ht' hpos
    exact ⟨{
      negative := ⟨a, ha⟩
      central := ⟨z, hz⟩
      positive := ⟨b, hb⟩
      product_eq := heq
      negative_depth := hat
      positive_depth := hbt }⟩)

end Langlands.Geometry.Building.ParahoricBuildingData
