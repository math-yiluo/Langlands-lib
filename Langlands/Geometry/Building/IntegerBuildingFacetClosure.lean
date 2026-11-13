import Langlands.Geometry.Building.IntegerBuildingFacetPartition
import Langlands.Geometry.Building.BuildingFacetIncidence

/-! # Closed facets in the integer-valued building over arbitrary fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- The image of the original apartment in the original quotient. -/
def apartmentImage : Set B.ReducedBuilding :=
  Set.range B.apartmentMap

/-- The chart of a translated original apartment. -/
def translatedApartmentMap (g : rationalPoints G) (a : B.Apartment) :
    B.ReducedBuilding :=
  g • B.apartmentMap a

theorem range_translatedApartmentMap (g : rationalPoints G) :
    Set.range (B.translatedApartmentMap g) = g • B.apartmentImage := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.smul_mem_smul_set ⟨a, rfl⟩
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem translatedApartmentMap_image_subset (g : rationalPoints G) (Fa : Set B.Apartment) :
    B.translatedApartmentMap g '' Fa ⊆ g • B.apartmentImage := by
  rintro _ ⟨a, _, rfl⟩
  exact (B.range_translatedApartmentMap g).le ⟨a, rfl⟩

theorem translatedApartmentMap_injective
    (hinj : Function.Injective B.apartmentMap) (g : rationalPoints G) :
    Function.Injective (B.translatedApartmentMap g) :=
  fun _ _ h => hinj (MulAction.injective g h)

theorem IsFacet.nonempty {Y : Set B.ReducedBuilding} (hY : B.IsFacet Y) :
    Y.Nonempty := by
  obtain ⟨g, Fa, ⟨a, rfl⟩, rfl⟩ := hY
  exact ⟨g • B.apartmentMap a, a, AffineRootSystem.mem_facet_self _ _, rfl⟩

/-- Face incidence in a common translated original apartment, including equality. -/
def FacetPrecedes (F C : B.BuildingFacet) : Prop :=
  ∃ (g : rationalPoints G) (Fa Ca : Set B.Apartment),
    AffineRootSystem.IsFaceOf B.affineRoots Fa Ca ∧
      F.val = B.translatedApartmentMap g '' Fa ∧
      C.val = B.translatedApartmentMap g '' Ca

/-- All full facets incident above a fixed full facet of the same quotient. -/
abbrev IncidentFacets (F : B.BuildingFacet) : Type u :=
  {C : B.BuildingFacet // B.FacetPrecedes F C}

theorem facetPrecedes_refl (F : B.BuildingFacet) : B.FacetPrecedes F F := by
  obtain ⟨g, Fa, hFa, hF⟩ := F.property
  exact ⟨g, Fa, Fa, hFa.isFaceOf_self, hF, hF⟩

/-- A coordinate change at one point agrees on the entire affine-root closed
facet of that point. The integer-valued data prove the required AS4 clause. -/
theorem exists_normalizer_eq_on_translated_facetClosure
    {a b : B.Apartment} (g : rationalPoints G)
    (hab : g • B.apartmentMap a = B.apartmentMap b) :
    ∃ n : normalizerPoints B.i, n • a = b ∧
      ∀ y ∈ AffineRootSystem.facetClosure B.affineRoots a,
        g • B.apartmentMap y = B.apartmentMap (n • y) := by
  have hab' :
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (g, a) =
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := by
    have h :
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (g * 1, a) =
          ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := hab
    simpa only [mul_one] using h
  obtain ⟨n, hn, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily g 1 a b).mp hab'
  have hp' : g⁻¹ * (n : rationalPoints G) ∈ B.sharpFixer {a} := by
    change g⁻¹ * 1 * (n : rationalPoints G) ∈ B.sharpFixer {a} at hp
    simpa only [mul_one] using hp
  refine ⟨n, hn, fun y hy => ?_⟩
  have hfix : (g⁻¹ * (n : rationalPoints G)) • B.apartmentMap y =
      B.apartmentMap y :=
    B.mem_fixer.mp (B.sharpFixer_le_fixer y
      (B.apartment.sharpFixer_singleton_le_of_mem_facetClosure
        B.affineRoot_mem_or_two_smul_mem hy hp'))
  have heq := congrArg (g • ·) hfix
  rw [mul_smul, smul_inv_smul, B.normalizer_smul_apartmentMap] at heq
  exact heq.symm

/-- The actual normalizer preserves face incidence without an AS5 premise. -/
theorem normalizer_smul_isFaceOf
    {Fa Ca : Set B.Apartment} (hFC : AffineRootSystem.IsFaceOf B.affineRoots Fa Ca)
    (n : normalizerPoints B.i) :
    AffineRootSystem.IsFaceOf B.affineRoots (n • Fa) (n • Ca) :=
  hFC.image (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n)

/-- Any translated apartment containing the upper facet gives simultaneous
affine face coordinates for both facets. No chart injectivity is needed. -/
theorem exists_apartment_faces_of_facetPrecedes
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C)
    (h : rationalPoints G) (hCsub : C.val ⊆ h • B.apartmentImage) :
    ∃ Fa Ca : Set B.Apartment, AffineRootSystem.IsFaceOf B.affineRoots Fa Ca ∧
      F.val = B.translatedApartmentMap h '' Fa ∧
      C.val = B.translatedApartmentMap h '' Ca := by
  obtain ⟨g, Fa, Ca, hAff, hF, hC⟩ := hFC
  obtain ⟨a, ha, hFa⟩ := hAff.2
  have haC : a ∈ Ca := ha ▸ AffineRootSystem.mem_facet_self _ _
  have hpoint : B.translatedApartmentMap g a ∈ C.val := by
    rw [hC]
    exact ⟨a, haC, rfl⟩
  obtain ⟨b, hb⟩ := (B.range_translatedApartmentMap h).ge (hCsub hpoint)
  change h • B.apartmentMap b = g • B.apartmentMap a at hb
  have hab : (h⁻¹ * g) • B.apartmentMap a = B.apartmentMap b := by
    rw [mul_smul, ← hb, inv_smul_smul]
  obtain ⟨n, _, heq⟩ := B.exists_normalizer_eq_on_translated_facetClosure (h⁻¹ * g) hab
  have himage (S : Set B.Apartment)
      (hS : S ⊆ AffineRootSystem.facetClosure B.affineRoots a) :
      B.translatedApartmentMap g '' S = B.translatedApartmentMap h '' (n • S) := by
    change (fun y => g • B.apartmentMap y) '' S =
      (fun y => h • B.apartmentMap y) '' (n • S)
    calc
      _ = (fun y => h • B.apartmentMap (n • y)) '' S := by
        apply Set.image_congr
        intro y hy
        have H := congrArg (h • ·) (heq y (hS hy))
        simpa only [mul_smul, smul_inv_smul] using H
      _ = _ := by
        change _ = (fun y => h • B.apartmentMap y) '' ((fun y => n • y) '' S)
        rw [Set.image_image]
  refine ⟨n • Fa, n • Ca, B.normalizer_smul_isFaceOf hAff n,
    hF.trans (himage Fa hFa), hC.trans (himage Ca ?_)⟩
  rw [← ha]
  exact AffineRootSystem.facet_subset_facetClosure _ _

/-- Every face lies in every translated apartment containing its upper facet. -/
theorem subset_apartment_of_facetPrecedes
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C)
    (h : rationalPoints G) (hCsub : C.val ⊆ h • B.apartmentImage) :
    F.val ⊆ h • B.apartmentImage := by
  obtain ⟨Fa, _, _, hF, _⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hFC h hCsub
  rw [hF]
  exact B.translatedApartmentMap_image_subset h Fa

/-- Reflecting incidence into prescribed coordinates retains the explicit
injectivity hypothesis on the original apartment map. -/
theorem facetPrecedes_iff_isFaceOf
    (hinj : Function.Injective B.apartmentMap)
    {F C : B.BuildingFacet} (h : rationalPoints G) {Fa Ca : Set B.Apartment}
    (hF : F.val = B.translatedApartmentMap h '' Fa)
    (hC : C.val = B.translatedApartmentMap h '' Ca) :
    B.FacetPrecedes F C ↔ AffineRootSystem.IsFaceOf B.affineRoots Fa Ca := by
  constructor
  · intro hFC
    obtain ⟨Fa', Ca', hAff, hF', hC'⟩ :=
      B.exists_apartment_faces_of_facetPrecedes hFC h
        (hC ▸ B.translatedApartmentMap_image_subset h Ca)
    have hFa : Fa' = Fa :=
      (B.translatedApartmentMap_injective hinj h).image_injective (hF'.symm.trans hF)
    have hCa : Ca' = Ca :=
      (B.translatedApartmentMap_injective hinj h).image_injective (hC'.symm.trans hC)
    rwa [hFa, hCa] at hAff
  · intro hAff
    exact ⟨h, Fa, Ca, hAff, hF, hC⟩

/-- The combinatorial closure is the union of all incident lower full facets.
Its exact affine-root description is proved below. -/
def buildingFacetClosure (C : B.BuildingFacet) : Set B.ReducedBuilding :=
  {x | ∃ F : B.BuildingFacet, B.FacetPrecedes F C ∧ x ∈ F.val}

theorem subset_buildingFacetClosure (C : B.BuildingFacet) :
    C.val ⊆ B.buildingFacetClosure C :=
  fun _ hx => ⟨C, B.facetPrecedes_refl C, hx⟩

theorem buildingFacetClosure_subset_apartment
    (C : B.BuildingFacet) (g : rationalPoints G) (hC : C.val ⊆ g • B.apartmentImage) :
    B.buildingFacetClosure C ⊆ g • B.apartmentImage := by
  rintro x ⟨F, hFC, hx⟩
  exact B.subset_apartment_of_facetPrecedes hFC g hC hx

theorem mem_buildingFacetClosure_iff_facetPrecedes (C : B.BuildingFacet)
    (x : B.ReducedBuilding) :
    x ∈ B.buildingFacetClosure C ↔ B.FacetPrecedes (B.buildingFacetAt x) C := by
  constructor
  · rintro ⟨F, hFC, hx⟩
    rwa [(B.buildingFacetAt_eq_iff_mem x F).mpr hx]
  · intro h
    exact ⟨B.buildingFacetAt x, h, B.mem_buildingFacetAt x⟩

theorem facetPrecedes_iff_nonempty_inter_buildingFacetClosure (F C : B.BuildingFacet) :
    B.FacetPrecedes F C ↔ (F.val ∩ B.buildingFacetClosure C).Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := F.property.nonempty B
    exact ⟨x, hx, F, h, hx⟩
  · rintro ⟨x, hx, D, hDC, hxd⟩
    have heq : F = D := Subtype.ext (F.property.eq_of_mem_mem B D.property hx hxd)
    exact heq ▸ hDC

theorem facetPrecedes_iff_subset_buildingFacetClosure (F C : B.BuildingFacet) :
    B.FacetPrecedes F C ↔ F.val ⊆ B.buildingFacetClosure C := by
  constructor
  · exact fun h _ hx => ⟨F, h, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := F.property.nonempty B
    exact (B.facetPrecedes_iff_nonempty_inter_buildingFacetClosure F C).mpr
      ⟨x, hx, h hx⟩

/-- The combinatorial closure is precisely the affine-root closed-facet image
in any presentation of the upper facet. No chart injectivity is assumed. -/
theorem buildingFacetClosure_eq_image
    (C : B.BuildingFacet) (g : rationalPoints G) (a : B.Apartment)
    (hC : C.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetClosure C =
      B.translatedApartmentMap g '' AffineRootSystem.facetClosure B.affineRoots a := by
  apply Set.Subset.antisymm
  · rintro _ ⟨F, ⟨h, Fa, Ca, hFace, hF, hC'⟩, hx⟩
    have hapoint : B.translatedApartmentMap g a ∈ C.val := by
      rw [hC]
      exact ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩
    rw [hC'] at hapoint
    obtain ⟨c, hc, hca⟩ := hapoint
    change h • B.apartmentMap c = g • B.apartmentMap a at hca
    have hca' : (g⁻¹ * h) • B.apartmentMap c = B.apartmentMap a := by
      rw [mul_smul, hca, inv_smul_smul]
    obtain ⟨n, hn, heq⟩ :=
      B.exists_normalizer_eq_on_translated_facetClosure (g⁻¹ * h) hca'
    rw [hF] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyc := B.apartment.mem_facetClosure_of_isFaceOf hFace hc hy
    have hyna : n • y ∈ AffineRootSystem.facetClosure B.affineRoots a := by
      rw [← hn]
      intro ψ hψ
      exact hyc _ ((AffineRootSystem.comp_mem_iff
        (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n) ψ).mpr hψ)
    refine ⟨n • y, hyna, ?_⟩
    have H := congrArg (g • ·) (heq y hyc)
    change g • B.apartmentMap (n • y) = h • B.apartmentMap y
    have H' : h • B.apartmentMap y = g • B.apartmentMap (n • y) := by
      simpa only [mul_smul, smul_inv_smul] using H
    exact H'.symm
  · rintro _ ⟨y, hy, rfl⟩
    let F : B.BuildingFacet :=
      ⟨B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots y,
        ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩
    refine ⟨F, ?_, y, AffineRootSystem.mem_facet_self _ _, rfl⟩
    exact ⟨g, _, _, ⟨AffineRootSystem.isFacet_facet _ _, a, rfl,
      AffineRootSystem.facet_subset_facetClosure_iff.mpr hy⟩, rfl, hC⟩

theorem buildingFacetAt_translatedApartmentMap (g : rationalPoints G) (a : B.Apartment) :
    (B.buildingFacetAt (B.translatedApartmentMap g a)).val =
      B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a := by
  let F : B.BuildingFacet :=
    ⟨B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a,
      ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩
  have hF : B.buildingFacetAt (B.translatedApartmentMap g a) = F :=
    (B.buildingFacetAt_eq_iff_mem _ F).mpr
      ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩
  exact congrArg Subtype.val hF

/-- At every translated apartment point, the closed facet has exactly the
original affine-root closure as its coordinate description. -/
theorem buildingFacetClosure_at_translatedApartmentMap
    (g : rationalPoints G) (a : B.Apartment) :
    B.buildingFacetClosure (B.buildingFacetAt (B.translatedApartmentMap g a)) =
      B.translatedApartmentMap g '' AffineRootSystem.facetClosure B.affineRoots a :=
  B.buildingFacetClosure_eq_image _ g a (B.buildingFacetAt_translatedApartmentMap g a)

end IntegerValuationBuildingData

/-- Exact affine-root description of combinatorial facet closures in the
original integer-valued quotient over arbitrary fields. -/
def IntegerBuildingFacetClosureStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G) (g : rationalPoints G) (a : B.Apartment),
    B.buildingFacetClosure (B.buildingFacetAt (B.translatedApartmentMap g a)) =
      B.translatedApartmentMap g '' AffineRootSystem.facetClosure B.affineRoots a

theorem integerBuildingFacetClosure : IntegerBuildingFacetClosureStatement.{u} := by
  intro k _ v G _ B g a
  exact B.buildingFacetClosure_at_translatedApartmentMap g a

end Langlands.Geometry.Building
