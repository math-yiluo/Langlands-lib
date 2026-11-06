import Langlands.Geometry.Building.AffineFacetCompactness
import Langlands.Geometry.Building.AffineFacetVertexGeneration
import Langlands.Geometry.Building.AffineFacetTransport
import Langlands.Geometry.Building.AffineRootSystemTransport
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Geometry.Building.FacetApartmentTransport
import Langlands.Geometry.Building.TitsFacetApartmentTransport
import Langlands.Geometry.Building.ApartmentRootCover

/-! # Pointwise fixation by zero-subgroup facet stabilizers -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.AffineRootSystem

/-- The compact-closure face-fixing criterion on an arbitrary affine torsor.
The root axioms supply compactness after choosing vector coordinates. -/
theorem eqOn_facetClosure_of_torsor_face_fixing
    {V A : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (p : A) (e : A ≃ᵃ[ℝ] A)
    (hfix : ∀ q ∈ facetClosure Ψ p, e '' facet Ψ q = facet Ψ q) :
    Set.EqOn e id (facetClosure Ψ p) := by
  let c : A ≃ᵃ[ℝ] V := AffineEquiv.constVSub ℝ p
  let Φ := transportedRoots c Ψ
  let f : V ≃ᵃ[ℝ] V := (c.symm.trans e).trans c
  have hΦ : IsAffineRootSystemWithRankZero Φ := hΨ.transport c
  have H := eqOn_facetClosure_of_face_fixing
    hΦ.isLocallyFiniteReflectionArrangement (c p)
    (hΦ.isCompact_facetClosure (c p)) (convex_facetClosure Φ (c p))
    f.toAffineMap f.toAffineMap.continuous_of_finiteDimensional
  have Hfix : ∀ z ∈ facetClosure Φ (c p), f '' facet Φ z = facet Φ z := by
    intro z hz
    obtain ⟨q, rfl⟩ := c.surjective z
    have hq : q ∈ facetClosure Ψ p := by
      have hz' := hz
      rw [← image_facetClosure_transportedRoots c Ψ p] at hz'
      exact c.injective.mem_set_image.mp hz'
    calc
      f '' facet Φ (c q) = c '' (e '' facet Ψ q) := by
        rw [← image_facet_transportedRoots c Ψ q, Set.image_image, Set.image_image]
        congr 1
        funext x
        simp [f]
      _ = c '' facet Ψ q := by rw [hfix q hq]
      _ = facet Φ (c q) := image_facet_transportedRoots c Ψ q
  intro q hq
  apply c.injective
  have hcq : c q ∈ facetClosure Φ (c p) := by
    rw [← image_facetClosure_transportedRoots c Ψ p]
    exact Set.mem_image_of_mem c hq
  have h := H Hfix hcq
  simpa [f] using h

end Langlands.Geometry.Building.AffineRootSystem

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual building facet of an apartment point. -/
def apartmentBuildingFacet (p : P.Apartment) :
    BuildingFacet P.toValuationBuildingData :=
  ⟨P.apartmentMap '' AffineRootSystem.facet P.affineRoots p,
    P.toValuationBuildingData.isFacet_image (AffineRootSystem.isFacet_facet _ _)⟩

@[simp] theorem apartmentBuildingFacet_val (p : P.Apartment) :
    (P.apartmentBuildingFacet p).val =
      P.apartmentMap '' AffineRootSystem.facet P.affineRoots p := rfl

/-- Apartment face incidence is actual building face incidence in the base chart. -/
theorem apartmentBuildingFacet_precedes {p q : P.Apartment}
    (hq : q ∈ AffineRootSystem.facetClosure P.affineRoots p) :
    FacetPrecedes P.toValuationBuildingData
      (P.apartmentBuildingFacet q) (P.apartmentBuildingFacet p) := by
  refine ⟨1, _, _, ⟨AffineRootSystem.isFacet_facet _ _, p, rfl,
    AffineRootSystem.facet_subset_facetClosure_iff.mpr hq⟩, ?_, ?_⟩ <;>
    simp only [apartmentBuildingFacet_val,
      ValuationBuildingData.translatedApartmentMap_one]

local instance : Fintype (relativeRoots P.i) := P.toValuationBuildingData.metricRootFintype
local instance : NormedAddCommGroup (TranslationSpace P.i) :=
  RootTranslationMetric.normedAddCommGroup P.i
local instance : NormedSpace ℝ (TranslationSpace P.i) :=
  RootTranslationMetric.normedSpace P.i
local instance : FiniteDimensional ℝ (TranslationSpace P.i) :=
  RootTranslationMetric.finiteDimensional P.i

/-- A normalizer element in the zero subgroup that stabilizes an apartment
facet fixes its entire closure pointwise. -/
theorem normalizer_eqOn_facetClosure
    (hD : P.SatisfiesApartmentAxioms)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (p : P.Apartment) (n : normalizerPoints P.i)
    (hn0 : (n : rationalPoints G) ∈ P.zeroSubgroup)
    (hnF : (⟨(n : rationalPoints G), hn0⟩ : P.zeroSubgroup) ∈
      P.facetZeroStabilizer (P.apartmentBuildingFacet p)) :
    Set.EqOn (P.toValuationBuildingData.normalizerAction n) id
      (AffineRootSystem.facetClosure P.affineRoots p) := by
  apply AffineRootSystem.eqOn_facetClosure_of_torsor_face_fixing
    hD.isAffineRootSystem_affineRoots p
  intro q hq
  have hnq := (hT.facetPrecedes_iff _ _).mp (P.apartmentBuildingFacet_precedes hq) hnF
  have himage : (n : rationalPoints G) •
      (P.apartmentBuildingFacet q).val = (P.apartmentBuildingFacet q).val := hnq
  apply hA.injective.image_injective
  rw [Set.image_image]
  have he : (fun x => P.apartmentMap (P.toValuationBuildingData.normalizerAction n x)) =
      fun x => (n : rationalPoints G) • P.apartmentMap x := by
    funext x
    exact (P.normalizer_smul_apartmentMap n x).symm
  rw [he]
  simpa only [apartmentBuildingFacet_val, ← Set.image_smul, Set.image_image] using himage

/-- A zero-subgroup stabilizer of a base-apartment facet fixes that facet
pointwise. The sharp fixer reduces the element to the normalizer. -/
theorem facetZeroStabilizer_smul_apartmentMap
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (p : P.Apartment) (k : P.zeroSubgroup)
    (hk : k ∈ P.facetZeroStabilizer (P.apartmentBuildingFacet p))
    {q : P.Apartment} (hq : q ∈ AffineRootSystem.facet P.affineRoots p) :
    (k : rationalPoints G) • P.apartmentMap q = P.apartmentMap q := by
  have hkp : P.apartmentMap p ∈
      (k : rationalPoints G) • P.toValuationBuildingData.apartmentImage := by
    have hFp : P.apartmentMap p ∈ (P.apartmentBuildingFacet p).val :=
      Set.mem_image_of_mem _ (AffineRootSystem.mem_facet_self _ _)
    have hfix : (k : rationalPoints G) • (P.apartmentBuildingFacet p).val =
        (P.apartmentBuildingFacet p).val := hk
    rw [← hfix] at hFp
    apply Set.smul_set_mono (s := (P.apartmentBuildingFacet p).val) (t := P.apartmentImage) _ hFp
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨r, hr, hrA, hrfix⟩ :=
    P.toValuationBuildingData.exists_sharpFixer_facet_smul_apartmentImage hD
      (AffineRootSystem.isFacet_facet _ _) (AffineRootSystem.mem_facet_self _ _)
      (ValuationBuildingData.IsApartment.smul _
        P.toValuationBuildingData.isApartment_apartmentImage (k : rationalPoints G)) hkp
  have hr0 : r ∈ P.zeroSubgroup :=
    P.zeroDatum.simplyConnectedImage_le_zeroSubgroup
      (P.sharpFixer_le_simplyConnectedImage hD _ hr)
  let r0 : P.zeroSubgroup := ⟨r, hr0⟩
  have hrF : r0 ∈ P.facetZeroStabilizer (P.apartmentBuildingFacet p) := by
    change r • (P.apartmentBuildingFacet p).val = (P.apartmentBuildingFacet p).val
    apply Set.Subset.antisymm
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      change r • P.apartmentMap y ∈ (P.apartmentBuildingFacet p).val
      rw [hrfix y hy]
      exact Set.mem_image_of_mem _ hy
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨P.apartmentMap y, Set.mem_image_of_mem _ hy, hrfix y hy⟩
  have hn : r * (k : rationalPoints G) ∈ normalizerPoints P.i :=
    (ValuationBuildingData.HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
      P.toValuationBuildingData hN _).mp (by simpa only [mul_smul] using hrA)
  let n : normalizerPoints P.i := ⟨r * (k : rationalPoints G), hn⟩
  have hn0 : (n : rationalPoints G) ∈ P.zeroSubgroup :=
    P.zeroSubgroup.mul_mem hr0 k.property
  have hnF : (⟨(n : rationalPoints G), hn0⟩ : P.zeroSubgroup) ∈
      P.facetZeroStabilizer (P.apartmentBuildingFacet p) := by
    have hm := (P.facetZeroStabilizer (P.apartmentBuildingFacet p)).mul_mem hrF hk
    change r0 * k ∈ P.facetZeroStabilizer (P.apartmentBuildingFacet p)
    exact hm
  have hnq := P.normalizer_eqOn_facetClosure hD hA hT p n hn0 hnF
    (AffineRootSystem.facet_subset_facetClosure _ _ hq)
  have heq : r • ((k : rationalPoints G) • P.apartmentMap q) =
      r • P.apartmentMap q := by
    rw [hrfix q hq]
    rw [← mul_smul]
    change (n : rationalPoints G) • P.apartmentMap q = P.apartmentMap q
    rw [P.normalizer_smul_apartmentMap]
    exact congrArg P.apartmentMap hnq
  exact MulAction.injective r heq

variable {P}

/-- Every actual apartment can be transported to the base apartment by an
element of the zero subgroup. -/
theorem IsBuildingTitsSystem.exists_zero_smul_apartmentImage
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) :
    ∃ t : P.zeroSubgroup,
      (t : rationalPoints G) • Y = P.toValuationBuildingData.apartmentImage := by
  obtain ⟨a, ha⟩ := hT.exists_restrictedApartment_eq hY
  obtain ⟨b, hb⟩ := hT.exists_restrictedApartment_eq
    P.toValuationBuildingData.isApartment_apartmentImage
  refine ⟨b * a⁻¹, hT.eq_of_facetStabilizersIn_eq
    (ValuationBuildingData.IsApartment.smul _ hY (b * a⁻¹))
    P.toValuationBuildingData.isApartment_apartmentImage ?_⟩
  rw [P.facetStabilizersIn_smul, ← ha,
    hT.isTitsSystem.image_conjugateSubgroup_restrictedApartment]
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hb

variable (P)

/-- The setwise stabilizer in the zero subgroup of any actual building facet
fixes each of its points. -/
theorem facetZeroStabilizer_smul_eq
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (Fc : BuildingFacet P.toValuationBuildingData) (k : P.zeroSubgroup)
    (hk : k ∈ P.facetZeroStabilizer Fc)
    {x : P.ReducedBuilding} (hx : x ∈ Fc.val) :
    (k : rationalPoints G) • x = x := by
  obtain ⟨g, Fa, hFa, hFc⟩ := Fc.property
  have hFcY : Fc.val ⊆ g • P.toValuationBuildingData.apartmentImage := by
    rw [hFc]
    rintro _ ⟨a, _, rfl⟩
    exact Set.smul_mem_smul_set ⟨a, rfl⟩
  obtain ⟨t, ht⟩ := hT.exists_zero_smul_apartmentImage
    (ValuationBuildingData.IsApartment.smul _
      P.toValuationBuildingData.isApartment_apartmentImage g)
  let Fd := P.zeroFacetTranslate t Fc
  have hFdA : Fd.val ⊆ P.toValuationBuildingData.apartmentImage := by
    rw [← ht]
    exact Set.smul_set_mono hFcY
  obtain ⟨z, hz⟩ := Fd.property.nonempty
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := hA.exists_isFacet_of_isFacet Fd.val Fd.property
    ⟨z, hz, hFdA hz⟩
  have hFd : Fd = P.apartmentBuildingFacet p := Subtype.ext hp
  have htk : t * k * t⁻¹ ∈ P.facetZeroStabilizer Fd := by
    rw [P.facetZeroStabilizer_zeroFacetTranslate]
    exact ⟨k, hk, rfl⟩
  have htx : (t : rationalPoints G) • x ∈ Fd.val :=
    Set.smul_mem_smul_set hx
  rw [hFd] at htk htx
  obtain ⟨q, hq, heq⟩ := htx
  have H := P.facetZeroStabilizer_smul_apartmentMap hD hN hA hT p
    (t * k * t⁻¹) htk hq
  rw [heq] at H
  have H' : (t : rationalPoints G) • ((k : rationalPoints G) • x) =
      (t : rationalPoints G) • x := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul,
      inv_smul_smul] using H
  exact MulAction.injective (t : rationalPoints G) H'

end Langlands.Geometry.Building.ParahoricBuildingData
