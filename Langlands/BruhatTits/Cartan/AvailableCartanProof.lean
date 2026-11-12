import Langlands.BruhatTits.SpecialCompact.WeylRepresentatives
import Langlands.BruhatTits.Cartan.AvailableCartanStatement
import Langlands.BruhatTits.Cartan.RelativeWeylChamber
import Langlands.Geometry.Building.IwasawaDecompositionProof
import Langlands.Geometry.Building.SpecialPointGlobalFixedLocus
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.Geometry.Building.AffineWeylFacetFixing
import Langlands.Geometry.Building.TitsFacetApartmentTransport
import Langlands.Geometry.Building.PointwiseFacetStabilizers
import Langlands.Geometry.Building.CommonApartmentConstruction
import Langlands.Geometry.Building.ApartmentFixedPointReduction
import Langlands.Geometry.Building.IwahoriWeylExactSequenceReduction
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.Geometry.Building.KPMinimalLeviZeroComparisonProof
import Langlands.Geometry.Building.ApartmentRootCover
import Langlands.Geometry.Building.SpecialPointVertices

/-!
# Proof of the corrected KP Theorem 5.2.1 on available Bruhat–Tits data

For a special vertex `x` of the apartment, `G(F) = P_x · j(D) · P_x`, two dominant
centralizer points give the same `P_x` double coset exactly when `z' z⁻¹ ∈ Z(F)^0`, and the
canonical dominant-quotient map is bijective.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.Cartan

section Datum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)

/-! ### Translations and the normalizer -/

/-- Conjugation by `n ∈ N(F)` transports the apartment translation of `z ∈ Z(F)` by the
linear part of `n`. -/
private theorem translation_conj (n : normalizerPoints B.i)
    {z z' : rationalPoints B.centralizer.Z}
    (h : B.centralizer.toNormalizer z' = n * B.centralizer.toNormalizer z * n⁻¹) :
    (Submodule.Quotient.mk (B.centralizer.translation z').toAdd : TranslationSpace B.i) =
      translationAction B.i n
        (Submodule.Quotient.mk (B.centralizer.translation z).toAdd) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty B.Apartment)
  have h1 := B.isOmegaCompatible.smul_eq_vadd z' x
  rw [h, mul_smul, mul_smul, B.isOmegaCompatible.smul_eq_vadd z,
    KPApartmentData.smul_vadd, smul_inv_smul] at h1
  exact (vadd_right_cancel x h1).symm

/-- The positive valuation `ω_Z(z')` of a conjugate `z'` of `z` by `n ∈ N(F)` has the root
values of `n • ω_Z(z)`. -/
private theorem eval_valuation_conj (n : normalizerPoints B.i)
    {z z' : rationalPoints B.centralizer.Z}
    (h : B.centralizer.toNormalizer z' = n * B.centralizer.toNormalizer z * n⁻¹)
    {α : characterLattice B.S} (hα : α ∈ relativeRoots B.i) :
    eval B.S α (centralizerValuation B.centralizer.s B.centralizer.bijective z').toAdd =
      eval B.S α
        (n • (centralizerValuation B.centralizer.s B.centralizer.bijective z).toAdd) := by
  have hq := congrArg (rootForm B.i ⟨α, hα⟩) (translation_conj B n h)
  rw [translationAction_mk, rootForm_mk, rootForm_mk] at hq
  change eval B.S α (centralizerTranslation B.centralizer.s B.centralizer.bijective z').toAdd =
    eval B.S α (n • (centralizerTranslation B.centralizer.s B.centralizer.bijective z).toAdd)
    at hq
  rw [centralizerTranslation_toAdd, centralizerTranslation_toAdd, smul_neg, map_neg,
    map_neg] at hq
  exact neg_injective hq

/-- A normalizer conjugate of a centralizer point is a centralizer point. -/
private theorem exists_conj_centralizer (n : normalizerPoints B.i)
    (z : rationalPoints B.centralizer.Z) :
    ∃ z' : rationalPoints B.centralizer.Z,
      B.centralizer.toNormalizer z' = n * B.centralizer.toNormalizer z * n⁻¹ := by
  apply B.exists_toNormalizer_eq_of_mem_centralizerPoints
  have hz : B.centralizer.toNormalizer z ∈
      (centralizerPoints B.i).subgroupOf (normalizerPoints B.i) := by
    rw [Subgroup.mem_subgroupOf, coe_centralizerToNormalizer,
      ← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2]
    exact ⟨z, rfl⟩
  exact (inferInstance : ((centralizerPoints B.i).subgroupOf
    (normalizerPoints B.i)).Normal).conj_mem _ hz n

/-- Points of `P_x` fix the image of `x` in the building. -/
private theorem parahoricAt_smul_apartmentMap (hA : B.SatisfiesApartmentAxioms)
    (x : B.Apartment) {p : rationalPoints G} (hp : p ∈ B.parahoricAt x) :
    p • B.apartmentMap x = B.apartmentMap x :=
  B.mem_fixer.mp (B.compactStabilizer_le_fixer _
    (B.parahoricAt_le_compactStabilizer hA.topologyCompatible x hp))

/-- Under Axiom 4.1.8 (2), an element of `G(F)^0` fixing the image of `x` lies in `P_x`. -/
private theorem mem_parahoricAt_of_smul_eq (hgen : B.HasZeroFixerGenerators)
    (x : B.Apartment) {g : rationalPoints G} (hg : g ∈ B.zeroSubgroup)
    (hgx : g • B.apartmentMap x = B.apartmentMap x) : g ∈ B.parahoricAt x :=
  hgen.zeroFixer_le_parahoric (Set.singleton_nonempty x)
    (fun f => by simpa only [Set.image_singleton] using
      (bddAbove_singleton : BddAbove ({f x} : Set ℝ)))
    (B.mem_zeroFixer.mpr ⟨hg, fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hgx⟩)

/-- `ν(z) = -ω_Z(z)` on every character. -/
private theorem eval_translation (α : characterLattice B.S)
    (z : rationalPoints B.centralizer.Z) :
    eval B.S α (B.centralizer.translation z).toAdd =
      -eval B.S α (centralizerValuation B.centralizer.s B.centralizer.bijective z).toAdd := by
  change eval B.S α (centralizerTranslation B.centralizer.s B.centralizer.bijective z).toAdd = _
  rw [centralizerTranslation_toAdd, map_neg]

end Datum

section Geometry

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)

/-- `G(F) = P_x N(F) P_x`: a common apartment of `x` and `g x`, moved to the base apartment
by the actual sharp fixer of `x` from both sides, gives an element of the apartment
stabilizer `N(F)`. -/
private theorem exists_parahoric_normalizer_parahoric
    (hN : B.HasNormalizerApartmentStabilizer) (x : B.Apartment)
    (hcommon : B.toValuationBuildingData.HasCommonApartmentWith (B.apartmentMap x))
    (g : rationalPoints G) :
    ∃ p₁ ∈ B.parahoricAt x, ∃ n : normalizerPoints B.i,
      ∃ p₂ ∈ B.parahoricAt x, g = p₁ * (n : rationalPoints G) * p₂ := by
  obtain ⟨Y, hY, hxY, hgxY⟩ := hcommon (g • B.apartmentMap x)
  obtain ⟨p₁, hp₁, hp₁Y⟩ :=
    B.toValuationBuildingData.exists_sharpFixer_smul_apartmentImage x hY hxY
  have hxY' : B.apartmentMap x ∈ g⁻¹ • Y := by
    simpa only [inv_smul_smul] using Set.smul_mem_smul_set (a := g⁻¹) hgxY
  obtain ⟨p₂, hp₂, hp₂Y⟩ := B.toValuationBuildingData.exists_sharpFixer_smul_apartmentImage x
    (ValuationBuildingData.IsApartment.smul _ hY g⁻¹) hxY'
  have h₂ : p₂⁻¹ • B.apartmentImage = g⁻¹ • Y := by rw [← hp₂Y, inv_smul_smul]
  have hn : p₁ * g * p₂⁻¹ ∈ normalizerPoints B.i := by
    apply (ValuationBuildingData.HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
      B.toValuationBuildingData hN _).mp
    rw [mul_smul, mul_smul, h₂, smul_inv_smul, hp₁Y]
  refine ⟨p₁⁻¹, (B.parahoricAt x).inv_mem (B.sharpFixer_le_parahoric _ hp₁),
    ⟨_, hn⟩, p₂, B.sharpFixer_le_parahoric _ hp₂, ?_⟩
  change g = p₁⁻¹ * (p₁ * g * p₂⁻¹) * p₂
  group

/-- At a special point, every `n ∈ N(F)` lies in `P_x j(z) P_x` for a dominant `z`. -/
private theorem exists_dominant_of_normalizer
    (hA : B.SatisfiesApartmentAxioms) (hgen : B.HasZeroFixerGenerators)
    (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) {x : B.Apartment}
    (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (n : normalizerPoints B.i) :
    ∃ p₁ ∈ B.parahoricAt x, ∃ z ∈ parahoricDominantSet B ν,
      ∃ p₂ ∈ B.parahoricAt x,
        (n : rationalPoints G) = p₁ * rationalPoints.map B.centralizer.j z * p₂ := by
  have hF := rootRankOneFactorization F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus
  have hsurj := SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective B hA hgen hF ν hν hx
  obtain ⟨m, hm, hmn⟩ := hsurj (QuotientGroup.mk n)
  have hc : ((m⁻¹ * n : normalizerPoints B.i) : rationalPoints G) ∈
      centralizerPoints B.i :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmn)
  obtain ⟨z, hz⟩ := B.exists_toNormalizer_eq_of_mem_centralizerPoints hc
  obtain ⟨w, hw⟩ := exists_relativeWeyl_smul_isDominantVector_of_reductive
    B.isConnectedReductive B.isMaximalSplitTorus hν
    (centralizerValuation B.centralizer.s B.centralizer.bijective z).toAdd
  obtain ⟨m', hm', hm'w⟩ := hsurj w
  obtain ⟨zd, hzd⟩ := exists_conj_centralizer B m' z
  have hdom : zd ∈ parahoricDominantSet B ν := by
    intro α hα
    rw [eval_valuation_conj B m' hzd hα.1]
    have h := hw α hα
    rwa [← hm'w, relativeWeyl_mk_smul] at h
  refine ⟨(m : rationalPoints G) * (m' : rationalPoints G)⁻¹,
    (B.parahoricAt x).mul_mem hm ((B.parahoricAt x).inv_mem hm'), zd, hdom, m', hm', ?_⟩
  have heq : n = m * m'⁻¹ * B.centralizer.toNormalizer zd * m' := by
    rw [hzd, hz]
    group
  have h := congrArg Subtype.val heq
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_centralizerToNormalizer] using h

/-- **Classification.** If `j(z') ∈ P_x j(z) P_x` for dominant `z, z'`, then
`z' z⁻¹ ∈ Z(F)^0`. -/
private theorem mem_centralizerZero_of_eq
    (hA : B.SatisfiesApartmentAxioms) (hgen : B.HasZeroFixerGenerators)
    (hN : B.HasNormalizerApartmentStabilizer) (hinj : Function.Injective B.apartmentMap)
    (htits : B.HasTitsSystem) (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) {x : B.Apartment}
    (hx : B.apartment.IsSpecialApartmentVertex x)
    {z z' : rationalPoints B.centralizer.Z}
    (hz : z ∈ parahoricDominantSet B ν) (hz' : z' ∈ parahoricDominantSet B ν)
    {a b : rationalPoints G} (ha : a ∈ B.parahoricAt x) (hb : b ∈ B.parahoricAt x)
    (hab : rationalPoints.map B.centralizer.j z' =
      a * rationalPoints.map B.centralizer.j z * b) :
    z' * z⁻¹ ∈ B.centralizerZero := by
  have hfixP : ∀ {p : rationalPoints G}, p ∈ B.parahoricAt x →
      p • B.apartmentMap x = B.apartmentMap x :=
    fun hp => parahoricAt_smul_apartmentMap B hA x hp
  have hG0 : B.zeroSubgroup.Normal := B.normal_zeroSubgroup
  have hP0 : B.parahoricAt x ≤ B.zeroSubgroup :=
    B.parahoric_le_zeroSubgroup hA {x}
  -- The second vertex `x' = z' x`.
  let x' : B.Apartment := B.centralizer.toNormalizer z' • x
  have hx'map : B.apartmentMap x' =
      rationalPoints.map B.centralizer.j z' • B.apartmentMap x :=
    (B.normalizer_smul_apartmentMap _ x).symm
  have hspec' : AffineRootSystem.IsSpecialPoint B.affineRoots x' := by
    have hroot : B.apartment.normalizerAffineEquiv (B.centralizer.toNormalizer z') ∈
        AffineRootSystem.rootStabilizer B.affineRoots :=
      (hA.range_le_extendedAffineWeylGroup ⟨_, rfl⟩).1
    exact (AffineRootSystem.isSpecialPoint_apply_iff hroot x).mpr hx.1
  have hvx' : AffineRootSystem.facet B.affineRoots x' = {x'} :=
    AffineRootSystem.isVertex_of_isSpecialPoint hA.isAffineRootSystem_affineRoots hspec'
  let Fc := B.apartmentBuildingFacet x
  let Fd := B.apartmentBuildingFacet x'
  have hFc : Fc.val = {B.apartmentMap x} := by
    change B.apartmentMap '' AffineRootSystem.facet B.affineRoots x = _
    rw [show AffineRootSystem.facet B.affineRoots x = {x} from hx.2, Set.image_singleton]
  have hFd : Fd.val = {B.apartmentMap x'} := by
    change B.apartmentMap '' AffineRootSystem.facet B.affineRoots x' = _
    rw [hvx', Set.image_singleton]
  -- The Tits system of Axiom 4.1.9 at some chamber.
  obtain ⟨c, hc, -⟩ :=
    hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
      |>.exists_regularPoint_closure x
  obtain ⟨W, _, π, Sgen, hT⟩ := htits _ ⟨c, hc, rfl⟩
  have hAapt := B.toValuationBuildingData.isApartment_apartmentImage
  have haA := ValuationBuildingData.IsApartment.smul _ hAapt a
  have hxA : B.apartmentMap x ∈ B.apartmentImage := ⟨x, rfl⟩
  have hx'A : B.apartmentMap x' ∈ B.apartmentImage := ⟨x', rfl⟩
  have hxaA : B.apartmentMap x ∈ a • B.apartmentImage := by
    rw [← hfixP ha]
    exact Set.smul_mem_smul_set hxA
  have hx'aA : B.apartmentMap x' ∈ a • B.apartmentImage := by
    rw [hx'map, hab, mul_smul, mul_smul, hfixP hb]
    exact Set.smul_mem_smul_set ⟨_, (B.normalizer_smul_apartmentMap
      (B.centralizer.toNormalizer z) x).symm⟩
  obtain ⟨k, hkc, hkd, hkA⟩ := hT.exists_twoFacet_smul_apartment_eq hAapt haA Fc Fd
    (by rw [hFc]; exact Set.singleton_subset_iff.mpr hxA)
    (by rw [hFd]; exact Set.singleton_subset_iff.mpr hx'A)
    (by rw [hFc]; exact Set.singleton_subset_iff.mpr hxaA)
    (by rw [hFd]; exact Set.singleton_subset_iff.mpr hx'aA)
  have hkx : (k : rationalPoints G) • B.apartmentMap x = B.apartmentMap x := by
    have h : (k : rationalPoints G) • Fc.val = Fc.val := B.mem_zeroStabilizerIn.mp hkc
    rwa [hFc, Set.smul_set_singleton, Set.singleton_eq_singleton_iff] at h
  have hkx' : (k : rationalPoints G) • B.apartmentMap x' = B.apartmentMap x' := by
    have h : (k : rationalPoints G) • Fd.val = Fd.val := B.mem_zeroStabilizerIn.mp hkd
    rwa [hFd, Set.smul_set_singleton, Set.singleton_eq_singleton_iff] at h
  have hkP : (k : rationalPoints G) ∈ B.parahoricAt x :=
    mem_parahoricAt_of_smul_eq B hgen x k.property hkx
  -- `n₀ = k⁻¹ a` stabilizes the base apartment and lies in `P_x`.
  have hn0 : (k : rationalPoints G)⁻¹ * a ∈ normalizerPoints B.i := by
    apply (ValuationBuildingData.HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
      B.toValuationBuildingData hN _).mp
    rw [mul_smul, ← hkA, inv_smul_smul]
  have hn0P : (k : rationalPoints G)⁻¹ * a ∈ B.parahoricAt x :=
    (B.parahoricAt x).mul_mem ((B.parahoricAt x).inv_mem hkP) ha
  -- `z'⁻¹ k z'` lies in `P_x`.
  have hcP : (rationalPoints.map B.centralizer.j z')⁻¹ * (k : rationalPoints G) *
      rationalPoints.map B.centralizer.j z' ∈ B.parahoricAt x := by
    apply mem_parahoricAt_of_smul_eq B hgen x
    · have h := hG0.conj_mem _ k.property (rationalPoints.map B.centralizer.j z')⁻¹
      simpa only [inv_inv] using h
    · rw [mul_smul, mul_smul, ← hx'map, hkx', hx'map, inv_smul_smul]
  -- `q = z'⁻¹ n₀ z` lies in `N(F) ∩ P_x`.
  have hq : (rationalPoints.map B.centralizer.j z')⁻¹ *
      ((k : rationalPoints G)⁻¹ * a * rationalPoints.map B.centralizer.j z) =
      ((rationalPoints.map B.centralizer.j z')⁻¹ * (k : rationalPoints G) *
        rationalPoints.map B.centralizer.j z')⁻¹ * b⁻¹ := by
    rw [hab]
    group
  have hqP : (rationalPoints.map B.centralizer.j z')⁻¹ *
      ((k : rationalPoints G)⁻¹ * a * rationalPoints.map B.centralizer.j z) ∈
        B.parahoricAt x := by
    rw [hq]
    exact (B.parahoricAt x).mul_mem ((B.parahoricAt x).inv_mem hcP)
      ((B.parahoricAt x).inv_mem hb)
  have hqN : (rationalPoints.map B.centralizer.j z')⁻¹ *
      ((k : rationalPoints G)⁻¹ * a * rationalPoints.map B.centralizer.j z) ∈
        normalizerPoints B.i :=
    (normalizerPoints B.i).mul_mem
      ((normalizerPoints B.i).inv_mem (B.centralizer.toNormalizer z').property)
      ((normalizerPoints B.i).mul_mem hn0 (B.centralizer.toNormalizer z).property)
  let n₀ : normalizerPoints B.i := ⟨_, hn0⟩
  let q : normalizerPoints B.i := ⟨_, hqN⟩
  have hrel : B.centralizer.toNormalizer z' =
      n₀ * q⁻¹ * (q * B.centralizer.toNormalizer z * q⁻¹) := by
    apply Subtype.ext
    change rationalPoints.map B.centralizer.j z' =
      ((k : rationalPoints G)⁻¹ * a) * ((rationalPoints.map B.centralizer.j z')⁻¹ *
        ((k : rationalPoints G)⁻¹ * a * rationalPoints.map B.centralizer.j z))⁻¹ *
      (((rationalPoints.map B.centralizer.j z')⁻¹ *
        ((k : rationalPoints G)⁻¹ * a * rationalPoints.map B.centralizer.j z)) *
        rationalPoints.map B.centralizer.j z *
        ((rationalPoints.map B.centralizer.j z')⁻¹ *
        ((k : rationalPoints G)⁻¹ * a * rationalPoints.map B.centralizer.j z))⁻¹)
    group
  obtain ⟨z'', hz''⟩ := exists_conj_centralizer B q z
  -- `z₀ = z' z''⁻¹ = n₀ q⁻¹` lies in `P_x`, so its translation vanishes.
  have hz0 : B.centralizer.toNormalizer (z' * z''⁻¹) = n₀ * q⁻¹ := by
    rw [map_mul, map_inv, hrel, hz'']
    group
  have hz0P : rationalPoints.map B.centralizer.j (z' * z''⁻¹) ∈ B.parahoricAt x := by
    have h := congrArg Subtype.val hz0
    rw [coe_centralizerToNormalizer] at h
    rw [h]
    exact (B.parahoricAt x).mul_mem hn0P ((B.parahoricAt x).inv_mem hqP)
  have ht0 : (Submodule.Quotient.mk (B.centralizer.translation (z' * z''⁻¹)).toAdd :
      TranslationSpace B.i) = 0 := by
    have h := hfixP hz0P
    rw [B.centralizer_smul_apartmentMap] at h
    exact vadd_right_cancel x ((hinj h).trans (zero_vadd _ x).symm)
  -- Root values: `ω(z') = q • ω(z)` on every root.
  have hroots : ∀ α ∈ relativeRoots B.i,
      eval B.S α
          (centralizerValuation B.centralizer.s B.centralizer.bijective z').toAdd =
        eval B.S α
          (q • (centralizerValuation B.centralizer.s B.centralizer.bijective
            z).toAdd) := by
    intro α hα
    have h0 := congrArg (rootForm B.i ⟨α, hα⟩) ht0
    rw [rootForm_mk, map_zero, map_mul, map_inv, toAdd_mul, toAdd_inv, map_add, map_neg,
      eval_translation, eval_translation] at h0
    rw [← eval_valuation_conj B q hz'' hα]
    linarith
  -- The dominant chamber is a fundamental domain.
  have hdom' : IsDominantVector B.i ν ((QuotientGroup.mk q : relativeWeylGroup B.i) •
      (centralizerValuation B.centralizer.s B.centralizer.bijective z).toAdd) := by
    intro α hα
    rw [relativeWeyl_mk_smul, ← hroots α hα.1]
    exact hz' α hα
  have hfix := relativeWeyl_smul_eq_of_isDominantVector_of_reductive
    B.isConnectedReductive B.isMaximalSplitTorus hν _ hz hdom'
  rw [relativeWeyl_mk_smul] at hfix
  -- Hence `z' z⁻¹` acts trivially on the apartment.
  have hct : (Submodule.Quotient.mk (B.centralizer.translation (z' * z⁻¹)).toAdd :
      TranslationSpace B.i) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, Geometry.Building.mem_rootAnnihilator]
    intro α hα
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, map_add, map_neg, eval_translation,
      eval_translation, hroots α hα, hfix]
    ring
  have haff : B.apartment.normalizerAffineEquiv
      (B.centralizer.toNormalizer (z' * z⁻¹)) = 1 := by
    rw [B.isOmegaCompatible.normalizerAffineEquiv_eq, hct]
    ext y
    simp
  -- And `j(z' z⁻¹) ∈ G(F)^0`.
  have hjG0 : rationalPoints.map B.centralizer.j (z' * z⁻¹) ∈ B.zeroSubgroup := by
    rw [map_mul, map_inv, hab]
    have h2 := hG0.conj_mem b (hP0 hb) (rationalPoints.map B.centralizer.j z)
    have h3 := B.zeroSubgroup.mul_mem (hP0 ha) h2
    simpa only [mul_assoc] using h3
  have hz1 := B.mem_rationalCommonNormKernel_of_normalizerAffineEquiv_eq_one haff
    (B.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel hjG0)
  have hcor := B.zeroDatum.minimalLeviZeroComparison.2
  change B.zeroDatum.zeroSubgroup.comap (rationalPoints.map B.centralizer.j) ⊓
    Plancherel.rationalCommonNormKernel B.centralizer.Z =
      B.zeroDatum.centralizerZero at hcor
  change z' * z⁻¹ ∈ B.zeroDatum.centralizerZero
  rw [← hcor]
  exact ⟨hjG0, hz1⟩

/-- The Cartan conclusions use apartment axioms, zero-fixer generation, the
normalizer apartment stabilizer, injectivity, a Tits system, and common
apartments with the given special vertex; no models or group assignment enter. -/
theorem parahoricCartanConclusions_of_buildingGeometry
    (hA : B.SatisfiesApartmentAxioms) (hgen : B.HasZeroFixerGenerators)
    (hN : B.HasNormalizerApartmentStabilizer) (hinj : Function.Injective B.apartmentMap)
    (htits : B.HasTitsSystem) (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) (x : B.Apartment)
    (hx : B.apartment.IsSpecialApartmentVertex x)
    (hcommon : B.toValuationBuildingData.HasCommonApartmentWith (B.apartmentMap x)) :
    ParahoricCartanConclusions B ν x := by
  have hcover : ∀ g : rationalPoints G, ∃ p₁ ∈ B.parahoricAt x,
      ∃ z ∈ parahoricDominantSet B ν, ∃ p₂ ∈ B.parahoricAt x,
        g = p₁ * rationalPoints.map B.centralizer.j z * p₂ := by
    intro g
    obtain ⟨p₁, hp₁, n, p₂, hp₂, rfl⟩ := exists_parahoric_normalizer_parahoric B hN x hcommon g
    obtain ⟨q₁, hq₁, z, hz, q₂, hq₂, hn⟩ := exists_dominant_of_normalizer B hA hgen ν hν hx.1 n
    refine ⟨p₁ * q₁, (B.parahoricAt x).mul_mem hp₁ hq₁, z, hz, q₂ * p₂,
      (B.parahoricAt x).mul_mem hq₂ hp₂, ?_⟩
    rw [hn]
    group
  have hdetect : ∀ z z' : parahoricDominantSet B ν,
      DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x)
          (rationalPoints.map B.centralizer.j z.val) =
        DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x)
          (rationalPoints.map B.centralizer.j z'.val) →
      z'.val * z.val⁻¹ ∈ B.centralizerZero := by
    intro z z' h
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.eq.mp h
    exact mem_centralizerZero_of_eq B hA hgen hN hinj htits ν hν hx z.2 z'.2 ha hb hab
  unfold ParahoricCartanConclusions
  dsimp only
  refine ⟨?_, fun z z' => ⟨fun h => hdetect z z' (DoubleCoset.mk_eq_of_doubleCoset_eq h),
    fun h => ?_⟩, ?_⟩
  · refine Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)
    obtain ⟨p₁, hp₁, z, hz, p₂, hp₂, rfl⟩ := hcover g
    exact Set.mul_mem_mul (Set.mul_mem_mul hp₁ ⟨z, hz, rfl⟩) hp₂
  · have hmk := parahoricDominantRespects B ν x z z' h
    exact (DoubleCoset.doubleCoset_eq_of_mem
      (DoubleCoset.mem_doubleCoset.mpr (DoubleCoset.eq.mp hmk))).symm
  · exact RestrictedRightQuotient.doubleCosetMap_bijective _ _ _ _ _
      (fun g => by
        obtain ⟨p₁, hp₁, z, hz, p₂, hp₂, rfl⟩ := hcover g
        exact ⟨⟨z, hz⟩, DoubleCoset.eq.mpr ⟨p₁, hp₁, p₂, hp₂, rfl⟩⟩)
      hdetect

/-- The canonical dominant `Z(F)^0` quotient parametrizes parahoric double
cosets under the precise building geometry inputs of the Cartan proof. -/
def parahoricCartanEquiv_of_buildingGeometry
    (hA : B.SatisfiesApartmentAxioms) (hgen : B.HasZeroFixerGenerators)
    (hN : B.HasNormalizerApartmentStabilizer) (hinj : Function.Injective B.apartmentMap)
    (htits : B.HasTitsSystem) (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) (x : B.Apartment)
    (hx : B.apartment.IsSpecialApartmentVertex x)
    (hcommon : B.toValuationBuildingData.HasCommonApartmentWith (B.apartmentMap x)) :
    ParahoricDominantQuotient B ν ≃
      DoubleCoset.Quotient (B.parahoricAt x : Set (rationalPoints G)) (B.parahoricAt x) :=
  parahoricDominantDoubleCosetEquiv B ν x
    (parahoricCartanConclusions_of_buildingGeometry B hA hgen hN hinj htits ν hν x hx
      hcommon).2.2

@[simp]
theorem parahoricCartanEquiv_of_buildingGeometry_class
    (hA : B.SatisfiesApartmentAxioms) (hgen : B.HasZeroFixerGenerators)
    (hN : B.HasNormalizerApartmentStabilizer) (hinj : Function.Injective B.apartmentMap)
    (htits : B.HasTitsSystem) (ν : cocharacterLattice B.S)
    (hν : IsGenericCocharacter B.i ν) (x : B.Apartment)
    (hx : B.apartment.IsSpecialApartmentVertex x)
    (hcommon : B.toValuationBuildingData.HasCommonApartmentWith (B.apartmentMap x))
    (z : parahoricDominantSet B ν) :
    parahoricCartanEquiv_of_buildingGeometry B hA hgen hN hinj htits ν hν x hx hcommon
        (parahoricDominantClass B ν z) =
      DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x)
        (rationalPoints.map B.centralizer.j z.val) := rfl

end Geometry

/-- **Corrected KP Theorem 5.2.1 for one datum.** If the datum satisfies the clauses of
the ten axioms of the corrected KP Definition 4.1.26 that concern `G` alone, then for every
generic `ν` and special apartment vertex `x` the three Cartan conclusions hold for `P_x`,
the corrected dominant set and `Z(F)^0`. -/
theorem parahoricCartanConclusions_of_satisfiesGroupAxioms
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (Dt : KPBuildingDatum G) (hD : Dt.SatisfiesGroupAxioms)
    (ν : cocharacterLattice Dt.base.S) (hν : IsGenericCocharacter Dt.base.i ν)
    (x : Dt.base.Apartment) (hx : Dt.base.apartment.IsSpecialApartmentVertex x) :
    ParahoricCartanConclusions Dt.base ν x :=
  parahoricCartanConclusions_of_buildingGeometry Dt.base
    hD.affineRootSystem.apartmentAxioms hD.rootGroupAction.zeroFixerGenerators
    hD.building.normalizerApartmentStabilizer
    hD.affineRootSystem.compatibleApartmentFacets.injective hD.titsSystem ν hν x hx
    (Dt.realization.hasCommonApartmentWith_of_isBuilding hD.building.isBuilding _)

/-- **Corrected KP Theorem 5.2.1** (with corrected (5.2.2)) under the full corrected KP
Definition 4.1.26 for one nonarchimedean local field and one connected reductive group. -/
theorem availableCartan : AvailableCartanStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx
  exact parahoricCartanConclusions_of_satisfiesGroupAxioms (𝔅.datum F G hG) h𝔅.groupAxioms
    ν hν x hx

end Langlands.BruhatTits.Cartan
