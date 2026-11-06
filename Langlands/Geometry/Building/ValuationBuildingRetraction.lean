import Langlands.Geometry.Building.PointwiseFacetStabilizers
import Langlands.Geometry.Building.FacetClosureLipschitz
import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.Geometry.Building.ApartmentFixedPointReduction
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # Retractions of the building onto the base apartment

KP Proposition 1.5.24 and Lemma 4.2.2 for the existing quotient `B(G)`: for a
chamber `C` of `A(S)`, every point `x` of `B(G)` is carried into `A(S)` by an
element of `G(F)` fixing `C` pointwise, and the resulting point of `A(S)` does
not depend on the element. The retraction `ρ_{A,C}` so obtained fixes `A(S)`,
does not increase any distance compatible with the translated apartment charts,
and preserves the distance from every point of the closure of `C`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- An affine automorphism fixing a chamber pointwise is the identity: the
chamber contains a small segment from its regular point in every direction. -/
theorem apply_eq_of_forall_mem_facet_of_isRegular
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) {y : A} (hy : IsRegular Ψ y)
    {e : A ≃ᵃ[ℝ] A} (he : ∀ z ∈ facet Ψ y, e z = z) (z : A) : e z = z := by
  have hy0 : e y = y := he y (mem_facet_self Ψ y)
  have hlin : ∀ v : V, e.linear v = v := by
    intro v
    obtain ⟨ε, hε, hs⟩ := exists_pos_of_eventually (eventually_sign_smul_vadd hΨ y v)
    have hmem : ε • v +ᵥ y ∈ facet Ψ y := fun ψ hψ => (hs ψ hψ (hy ψ hψ)).symm
    have h1 := he _ hmem
    rw [AffineEquiv.map_vadd, hy0] at h1
    have h2 : e.linear (ε • v) = ε • v := vadd_right_cancel y h1
    rw [map_smul] at h2
    exact smul_right_injective V hε.ne' h2
  rw [← vsub_vadd z y, AffineEquiv.map_vadd, hlin, hy0]

end Langlands.Geometry.Building.AffineRootSystem

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G}

/-- Under AS 6, a facet of the building meeting an apartment lies in it. -/
theorem HasCompatibleApartmentFacets.subset_of_inter_nonempty
    (hA : B.HasCompatibleApartmentFacets)
    {Y Fc : Set B.ReducedBuilding} (hY : B.IsApartment Y) (hF : B.IsFacet Fc)
    (hne : (Fc ∩ Y).Nonempty) : Fc ⊆ Y := by
  obtain ⟨g, rfl⟩ := hY
  obtain ⟨z, hzF, hzY⟩ := hne
  have hF' : B.IsFacet ((g⁻¹ • ·) '' Fc) := IsFacet.smul B hF g⁻¹
  have hzA : g⁻¹ • z ∈ B.apartmentImage := by
    rwa [Set.mem_smul_set_iff_inv_smul_mem] at hzY
  obtain ⟨Fa, -, hFa⟩ := hA.exists_isFacet_of_isFacet _ hF'
    ⟨g⁻¹ • z, ⟨z, hzF, rfl⟩, hzA⟩
  intro x hx
  have hx' : g⁻¹ • x ∈ B.apartmentMap '' Fa := hFa ▸ ⟨x, hx, rfl⟩
  obtain ⟨b, -, hb⟩ := hx'
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← hb]
  exact ⟨b, rfl⟩

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.Geometry.Building.ParahoricBuildingData

open AffineRootSystem.GalleryGeometry

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The facet `g · F(p)` of the building, for the apartment facet `F(p)` of a
point `p` of `A(S)`. -/
def translatedApartmentFacet (g : rationalPoints G) (p : P.Apartment) :
    BuildingFacet P.toValuationBuildingData :=
  ⟨P.translatedApartmentMap g '' AffineRootSystem.facet P.affineRoots p,
    ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩

theorem smul_apartmentMap_mem_translatedApartmentFacet (g : rationalPoints G)
    {p q : P.Apartment} (hq : q ∈ AffineRootSystem.facet P.affineRoots p) :
    g • P.apartmentMap q ∈ (P.translatedApartmentFacet g p).val :=
  ⟨q, hq, rfl⟩

/-- Face incidence in a translated apartment chart is face incidence of building facets. -/
theorem translatedApartmentFacet_precedes (g : rationalPoints G) {p q : P.Apartment}
    (hq : q ∈ AffineRootSystem.facetClosure P.affineRoots p) :
    FacetPrecedes P.toValuationBuildingData
      (P.translatedApartmentFacet g q) (P.translatedApartmentFacet g p) :=
  ⟨g, _, _, ⟨AffineRootSystem.isFacet_facet _ _, p, rfl,
    AffineRootSystem.facet_subset_facetClosure_iff.mpr hq⟩, rfl, rfl⟩

variable {P}

/-- An apartment containing the point `g · p` contains `g · q` for every `q` in
the closure of the facet of `p`. -/
theorem smul_apartmentMap_mem_of_mem_facetClosure
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) (g : rationalPoints G)
    {p : P.Apartment} (hpY : g • P.apartmentMap p ∈ Y) {q : P.Apartment}
    (hq : q ∈ AffineRootSystem.facetClosure P.affineRoots p) :
    g • P.apartmentMap q ∈ Y := by
  have hgA : P.IsApartment (g • P.apartmentImage) := ⟨g, rfl⟩
  have hFgA : (P.translatedApartmentFacet g p).val ⊆ g • P.apartmentImage := by
    rintro _ ⟨b, -, rfl⟩
    exact Set.smul_mem_smul_set ⟨b, rfl⟩
  have hFY : (P.translatedApartmentFacet g p).val ⊆ Y :=
    hA.subset_of_inter_nonempty hY (P.translatedApartmentFacet g p).property
      ⟨_, P.smul_apartmentMap_mem_translatedApartmentFacet g
        (AffineRootSystem.mem_facet_self _ p), hpY⟩
  obtain ⟨k, hk, -, hkY⟩ :=
    hT.exists_twoFacet_smul_apartment_eq hgA hY _ _ hFgA hFgA hFY hFY
  have hkq := (hT.facetPrecedes_iff _ _).mp (P.translatedApartmentFacet_precedes g hq) hk
  have hfix := P.facetZeroStabilizer_smul_eq hD hN hA hT _ k hkq
    (P.smul_apartmentMap_mem_translatedApartmentFacet g (AffineRootSystem.mem_facet_self _ q))
  rw [← hfix, ← hkY]
  exact Set.smul_mem_smul_set (Set.smul_mem_smul_set ⟨q, rfl⟩)

/-- Two elements fixing a chamber `C` of `A(S)` pointwise and both carrying `x`
into `A(S)` give the same point (the well-definedness in KP Proposition 1.5.24).
The two apartments `h₁⁻¹ · A(S)` and `h₂⁻¹ · A(S)` share `C` and the facet of `x`. -/
theorem smul_eq_smul_of_forall_mem_facet
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    {y : P.Apartment} (hy : IsRegular P.affineRoots y)
    {h₁ h₂ : rationalPoints G}
    (h₁y : ∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      h₁ • P.apartmentMap z = P.apartmentMap z)
    (h₂y : ∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      h₂ • P.apartmentMap z = P.apartmentMap z)
    {x : P.ReducedBuilding} (h₁x : h₁ • x ∈ P.apartmentImage)
    (h₂x : h₂ • x ∈ P.apartmentImage) :
    h₁ • x = h₂ • x := by
  have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  have hY : ∀ h : rationalPoints G, P.IsApartment (h⁻¹ • P.apartmentImage) :=
    fun h => ⟨h⁻¹, rfl⟩
  have hxY : ∀ {h : rationalPoints G}, h • x ∈ P.apartmentImage →
      x ∈ h⁻¹ • P.apartmentImage := fun {h} hx => by
    rwa [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  have hCY : ∀ {h : rationalPoints G}, (∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      h • P.apartmentMap z = P.apartmentMap z) →
        (P.apartmentBuildingFacet y).val ⊆ h⁻¹ • P.apartmentImage := by
    rintro h hh _ ⟨z, hz, rfl⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, hh z hz]
    exact ⟨z, rfl⟩
  obtain ⟨Fx, hxF, hFY₁⟩ := P.exists_buildingFacet_mem_subset_apartment (hY h₁) (hxY h₁x)
  have hFY₂ : Fx.val ⊆ h₂⁻¹ • P.apartmentImage :=
    hA.subset_of_inter_nonempty (hY h₂) Fx.property ⟨x, hxF, hxY h₂x⟩
  obtain ⟨k, hkC, hkF, hkY⟩ := hT.exists_twoFacet_smul_apartment_eq (hY h₂) (hY h₁)
    (P.apartmentBuildingFacet y) Fx (hCY h₂y) hFY₂ (hCY h₁y) hFY₁
  have hkx : (k : rationalPoints G) • x = x :=
    P.facetZeroStabilizer_smul_eq hD hN hA hT Fx k hkF hxF
  have hkC' : ∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      (k : rationalPoints G) • P.apartmentMap z = P.apartmentMap z := fun z hz =>
    P.facetZeroStabilizer_smul_eq hD hN hA hT _ k hkC ⟨z, hz, rfl⟩
  set m := h₁ * (k : rationalPoints G) * h₂⁻¹ with hm_def
  have hmA : m • P.apartmentImage = P.apartmentImage := by
    rw [hm_def, mul_smul, mul_smul, hkY, smul_inv_smul]
  have hm : m ∈ normalizerPoints P.i :=
    (ValuationBuildingData.HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
      P.toValuationBuildingData hN m).mp hmA
  let n : normalizerPoints P.i := ⟨m, hm⟩
  have hmz : ∀ z : P.Apartment, m • P.apartmentMap z = P.apartmentMap (n • z) :=
    fun z => P.normalizer_smul_apartmentMap n z
  have hny : ∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      P.toValuationBuildingData.normalizerAction n z = z := by
    intro z hz
    apply hA.injective
    rw [ValuationBuildingData.normalizerAction_apply, ← hmz, hm_def, mul_smul, mul_smul,
      inv_smul_eq_iff.mpr (h₂y z hz).symm, hkC' z hz, h₁y z hz]
  have hn1 := AffineRootSystem.apply_eq_of_forall_mem_facet_of_isRegular hΨ hy hny
  obtain ⟨β, hβ⟩ := h₂x
  have hmx : m • (h₂ • x) = h₂ • x := by
    rw [← hβ, hmz, ← ValuationBuildingData.normalizerAction_apply, hn1]
  calc h₁ • x = h₁ • ((k : rationalPoints G) • x) := by rw [hkx]
    _ = m • (h₂ • x) := by rw [hm_def, mul_smul, mul_smul, inv_smul_smul]
    _ = h₂ • x := hmx

variable (P)

/-- Every apartment containing a point `y` of `A(S)` is carried onto `A(S)` by
an element of `G(F)^0` fixing the facet of `y` pointwise (the sharp fixer). -/
theorem exists_zero_forall_mem_facet_smul_eq
    (hD : P.SatisfiesApartmentAxioms) (y : P.Apartment)
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hyY : P.apartmentMap y ∈ Y) :
    ∃ r : rationalPoints G, r ∈ P.zeroSubgroup ∧
      (∀ z ∈ AffineRootSystem.facet P.affineRoots y,
        r • P.apartmentMap z = P.apartmentMap z) ∧
      r • Y = P.apartmentImage := by
  obtain ⟨r, hr, hrY, hrfix⟩ :=
    P.toValuationBuildingData.exists_sharpFixer_facet_smul_apartmentImage hD
      (AffineRootSystem.isFacet_facet _ y) (AffineRootSystem.mem_facet_self _ y) hY hyY
  exact ⟨r, P.zeroDatum.simplyConnectedImage_le_zeroSubgroup
    (P.sharpFixer_le_simplyConnectedImage hD _ hr), hrfix, hrY⟩

variable {P}

/-- An element of `G(F)^0` fixing the facet of `y` pointwise fixes every point
of its closure. -/
theorem smul_apartmentMap_eq_of_mem_facetClosure
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    {y a : P.Apartment} (ha : a ∈ AffineRootSystem.facetClosure P.affineRoots y)
    {r : rationalPoints G} (hr0 : r ∈ P.zeroSubgroup)
    (hr : ∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      r • P.apartmentMap z = P.apartmentMap z) :
    r • P.apartmentMap a = P.apartmentMap a := by
  let r0 : P.zeroSubgroup := ⟨r, hr0⟩
  have hrF : r0 ∈ P.facetZeroStabilizer (P.apartmentBuildingFacet y) := by
    change r • (P.apartmentBuildingFacet y).val = (P.apartmentBuildingFacet y).val
    apply Set.Subset.antisymm
    · rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      change r • P.apartmentMap z ∈ (P.apartmentBuildingFacet y).val
      rw [hr z hz]
      exact Set.mem_image_of_mem _ hz
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨P.apartmentMap z, Set.mem_image_of_mem _ hz, hr z hz⟩
  have hra := (hT.facetPrecedes_iff _ _).mp (P.apartmentBuildingFacet_precedes ha) hrF
  exact P.facetZeroStabilizer_smul_eq hD hN hA hT _ r0 hra
    ⟨a, AffineRootSystem.mem_facet_self _ a, rfl⟩

variable (P)

/-- Each point of `B(G)` is carried into `A(S)` by an element of `G(F)^0`
fixing the facet of `y` pointwise. -/
theorem exists_retractionPoint
    (hD : P.SatisfiesApartmentAxioms)
    (hcommon : ∀ x : P.ReducedBuilding, P.HasCommonApartmentWith x)
    (y : P.Apartment) (x : P.ReducedBuilding) :
    ∃ b : P.Apartment, ∃ r : rationalPoints G, r ∈ P.zeroSubgroup ∧
      (∀ z ∈ AffineRootSystem.facet P.affineRoots y,
        r • P.apartmentMap z = P.apartmentMap z) ∧
      r • x = P.apartmentMap b := by
  obtain ⟨Y, hY, hyY, hxY⟩ := hcommon (P.apartmentMap y) x
  obtain ⟨r, hr0, hrfix, hrY⟩ := P.exists_zero_forall_mem_facet_smul_eq hD y hY hyY
  have hrx : r • x ∈ P.apartmentImage := hrY ▸ Set.smul_mem_smul_set hxY
  obtain ⟨b, hb⟩ := hrx
  exact ⟨b, r, hr0, hrfix, hb.symm⟩

/-- The retraction `ρ_{A,C} : B(G) → A(S)` centred at the facet of `y` (KP
Proposition 1.5.24 and Definition 1.5.25); it is meaningful when `y` is regular,
so that this facet is a chamber. -/
def chamberRetraction
    (hD : P.SatisfiesApartmentAxioms)
    (hcommon : ∀ x : P.ReducedBuilding, P.HasCommonApartmentWith x)
    (y : P.Apartment) (x : P.ReducedBuilding) : P.Apartment :=
  (P.exists_retractionPoint hD hcommon y x).choose

variable {P}

/-- Any element fixing the chamber pointwise and carrying `x` into `A(S)` carries
`x` to its retraction. -/
theorem apartmentMap_chamberRetraction
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (hcommon : ∀ x : P.ReducedBuilding, P.HasCommonApartmentWith x)
    {y : P.Apartment} (hy : IsRegular P.affineRoots y)
    {h : rationalPoints G}
    (hh : ∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      h • P.apartmentMap z = P.apartmentMap z)
    {x : P.ReducedBuilding} (hx : h • x ∈ P.apartmentImage) :
    P.apartmentMap (P.chamberRetraction hD hcommon y x) = h • x := by
  obtain ⟨r, -, hrfix, hrx⟩ := (P.exists_retractionPoint hD hcommon y x).choose_spec
  rw [chamberRetraction, ← hrx]
  exact P.smul_eq_smul_of_forall_mem_facet hD hN hA hT hy hrfix hh
    (hrx ▸ ⟨_, rfl⟩) hx

local instance retractionRootFintype : Fintype (relativeRoots P.i) :=
  P.toValuationBuildingData.metricRootFintype
local instance retractionNormedAddCommGroup : NormedAddCommGroup (TranslationSpace P.i) :=
  RootTranslationMetric.normedAddCommGroup P.i
local instance retractionNormedSpace : NormedSpace ℝ (TranslationSpace P.i) :=
  RootTranslationMetric.normedSpace P.i
local instance retractionFiniteDimensional : FiniteDimensional ℝ (TranslationSpace P.i) :=
  RootTranslationMetric.finiteDimensional P.i
local instance retractionMetricSpace : MetricSpace P.Apartment :=
  P.toValuationBuildingData.apartmentMetricSpace
local instance retractionNormedAddTorsor : NormedAddTorsor (TranslationSpace P.i) P.Apartment :=
  P.toValuationBuildingData.apartmentNormedAddTorsor

/-- KP Lemma 4.2.2 for an arbitrary distance `d` on `B(G)` that is the Euclidean
root metric in every translated apartment chart: for every point `a` of `A(S)`
there is a retraction `ρ : B(G) → A(S)` fixing `A(S)`, not increasing `d`, and
preserving the `d`-distance from `a`. The retraction is `ρ_{A,C}` for a chamber
`C` of `A(S)` whose closure contains `a`. -/
theorem exists_apartmentRetraction
    (hcommon : ∀ x : P.ReducedBuilding, P.HasCommonApartmentWith x)
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    (hTits : P.HasTitsSystem)
    {d : P.ReducedBuilding → P.ReducedBuilding → ℝ}
    (hd : ∀ (g : rationalPoints G) (a b : P.Apartment),
      d (g • P.apartmentMap a) (g • P.apartmentMap b) = dist a b)
    (a : P.Apartment) :
    ∃ ρ : P.ReducedBuilding → P.Apartment,
      (∀ b : P.Apartment, ρ (P.apartmentMap b) = b) ∧
        (∀ x x' : P.ReducedBuilding, dist (ρ x) (ρ x') ≤ d x x') ∧
        ∀ x : P.ReducedBuilding, dist a (ρ x) = d (P.apartmentMap a) x := by
  have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨y, hy, hay⟩ := hΨ.exists_regularPoint_closure a
  obtain ⟨W, _, π, Sgen, hT⟩ := hTits _ ⟨y, hy, rfl⟩
  set ρ := P.chamberRetraction hD hcommon y with hρ
  have hspec : ∀ {h : rationalPoints G}, (∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      h • P.apartmentMap z = P.apartmentMap z) →
        ∀ {x : P.ReducedBuilding}, h • x ∈ P.apartmentImage →
          P.apartmentMap (ρ x) = h • x :=
    fun hh _ hx => apartmentMap_chamberRetraction hD hN hA hT hcommon hy hh hx
  have hdist : ∀ {h : rationalPoints G}, (∀ z ∈ AffineRootSystem.facet P.affineRoots y,
      h • P.apartmentMap z = P.apartmentMap z) →
        ∀ {x x' : P.ReducedBuilding}, h • x ∈ P.apartmentImage →
          h • x' ∈ P.apartmentImage → dist (ρ x) (ρ x') = d x x' := by
    intro h hh x x' hx hx'
    rw [← hd h⁻¹, hspec hh hx, hspec hh hx', inv_smul_smul, inv_smul_smul]
  refine ⟨ρ, fun b => ?_, fun x x' => ?_, fun x => ?_⟩
  · apply hA.injective
    rw [hspec (h := 1) (fun z _ => one_smul _ _) (by rw [one_smul]; exact ⟨b, rfl⟩),
      one_smul]
  · obtain ⟨Y, ⟨g, rfl⟩, hxY, hx'Y⟩ := hcommon x x'
    obtain ⟨_, ⟨p, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hxY
    obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hx'Y
    rw [hd]
    refine AffineRootSystem.dist_le_of_forall_mem_facetClosure (Ψ := P.affineRoots)
      hΨ.finite_bounded_at (f := fun u => ρ (g • P.apartmentMap u)) ?_ p q
    intro p₀ u v hu hv
    obtain ⟨Y', hY', hyY', hpY'⟩ := hcommon (P.apartmentMap y) (g • P.apartmentMap p₀)
    obtain ⟨r, -, hrfix, hrY'⟩ := P.exists_zero_forall_mem_facet_smul_eq hD y hY' hyY'
    have hmem : ∀ w ∈ AffineRootSystem.facetClosure P.affineRoots p₀,
        r • (g • P.apartmentMap w) ∈ P.apartmentImage := fun w hw => by
      rw [← hrY']
      exact Set.smul_mem_smul_set
        (smul_apartmentMap_mem_of_mem_facetClosure hD hN hA hT hY' g hpY' hw)
    exact (hdist hrfix (hmem u hu) (hmem v hv)).trans_le (hd g u v).le
  · obtain ⟨Y, hY, hyY, hxY⟩ := hcommon (P.apartmentMap y) x
    obtain ⟨r, hr0, hrfix, hrY⟩ := P.exists_zero_forall_mem_facet_smul_eq hD y hY hyY
    have hra := smul_apartmentMap_eq_of_mem_facetClosure hD hN hA hT hay hr0 hrfix
    have hrx : r • x ∈ P.apartmentImage := hrY ▸ Set.smul_mem_smul_set hxY
    rw [← hd r⁻¹ a (ρ x), hspec hrfix hrx, inv_smul_smul, inv_smul_eq_iff.mpr hra.symm]

end Langlands.Geometry.Building.ParahoricBuildingData
