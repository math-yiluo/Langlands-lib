import Langlands.Geometry.Building.ApartmentFacetConstruction
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.BruhatTits.IntegralModels.FacetParabolicOrder

/-! # Incidence of facets in the actual valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V A : Type u} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {F C D : Set A}

/-- The affine face relation includes each facet itself. -/
theorem IsFacet.isFaceOf_self (hF : IsFacet Ψ F) : IsFaceOf Ψ F F := by
  obtain ⟨x, rfl⟩ := hF
  exact ⟨isFacet_facet _ _, x, rfl, facet_subset_facetClosure _ _⟩

/-- Face incidence is transitive for the existing affine-root closure formula. -/
theorem IsFaceOf.trans (hFC : IsFaceOf Ψ F C) (hCD : IsFaceOf Ψ C D) :
    IsFaceOf Ψ F D := by
  obtain ⟨hF, c, hc, hFc⟩ := hFC
  obtain ⟨_, d, hd, hCd⟩ := hCD
  refine ⟨hF, d, hd, fun x hx => ?_⟩
  exact mem_facetClosure_trans (hCd (hc ▸ mem_facet_self Ψ c)) (hFc hx)

/-- Mutual closed-side containment identifies the affine facets. -/
theorem IsFaceOf.antisymm (hFC : IsFaceOf Ψ F C) (hCF : IsFaceOf Ψ C F) :
    F = C := by
  obtain ⟨_, c, hc, hFc⟩ := hFC
  obtain ⟨_, f, hf, hCf⟩ := hCF
  have hfc := hFc (hf ▸ mem_facet_self Ψ f)
  have hcf := hCf (hc ▸ mem_facet_self Ψ c)
  rw [← hf, ← hc, facet_eq_facet_iff]
  intro ψ hψ
  rcases hfc ψ hψ with hf0 | hfc'
  · rcases hcf ψ hψ with hc0 | hcf'
    · exact hf0.trans hc0.symm
    · exact hcf'.symm
  · exact hfc'

/-- An affine-root-preserving automorphism preserves face incidence. -/
theorem IsFaceOf.image (hFC : IsFaceOf Ψ F C) {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) : IsFaceOf Ψ (e '' F) (e '' C) := by
  obtain ⟨⟨f, hf⟩, c, hc, hFc⟩ := hFC
  refine ⟨⟨e f, ?_⟩, e c, ?_, ?_⟩
  · rw [← image_facet he, hf]
  · rw [← image_facet he, hc]
  · rintro _ ⟨y, hy, rfl⟩ ψ hψ
    exact hFc hy _ ((comp_mem_iff he ψ).2 hψ)

end AffineRootSystem

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- At a point in a closed facet, every sharp-fixer generator of its upper
facet remains a depth-zero generator. Only AS4 is used. -/
theorem sharpFixer_singleton_le_of_mem_facetClosure
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots, ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {x y : D.Apartment} (hyx : y ∈ AffineRootSystem.facetClosure D.affineRoots x) :
    D.sharpFixer {x} ≤ D.sharpFixer {y} := by
  unfold sharpFixer
  apply iSup_mono
  intro a
  rw [D.rootFixer_singleton, D.rootFixer_singleton]
  exact (D.filtration_comparison_of_mem_facetClosure hAS4 hyx a.property).2

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- A quotient coordinate change at one point agrees on its whole closed
facet, and therefore on every face of that facet. -/
theorem exists_normalizer_eq_on_translated_facetClosure
    (hD : B.SatisfiesApartmentAxioms)
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
        hD.mem_or_two_smul_mem hy hp'))
  have heq := congrArg (g • ·) hfix
  rw [mul_smul, smul_inv_smul, B.normalizer_smul_apartmentMap] at heq
  exact heq.symm

/-- The normalizer action preserves affine face incidence, using AS5. -/
theorem normalizer_smul_isFaceOf
    (hD : B.SatisfiesApartmentAxioms)
    {Fa Ca : Set B.Apartment} (hFC : AffineRootSystem.IsFaceOf B.affineRoots Fa Ca)
    (n : normalizerPoints B.i) :
    AffineRootSystem.IsFaceOf B.affineRoots (n • Fa) (n • Ca) :=
  hFC.image (hD.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1


/-- Every incident pair has affine face coordinates in any translated apartment
containing the upper facet. No chart injectivity is assumed. -/
theorem exists_apartment_faces_of_facetPrecedes
    (hD : B.SatisfiesApartmentAxioms)
    {Fc Cc : BuildingFacet B} (hFC : FacetPrecedes B Fc Cc)
    (h : rationalPoints G) (hCsub : Cc.val ⊆ h • B.apartmentImage) :
    ∃ Fa Ca : Set B.Apartment, AffineRootSystem.IsFaceOf B.affineRoots Fa Ca ∧
      Fc.val = B.translatedApartmentMap h '' Fa ∧
      Cc.val = B.translatedApartmentMap h '' Ca := by
  obtain ⟨g, Fa, Ca, hAff, hF, hC⟩ := hFC
  obtain ⟨a, ha, hFa⟩ := hAff.2
  have haC : a ∈ Ca := ha ▸ AffineRootSystem.mem_facet_self _ _
  have hpoint : B.translatedApartmentMap g a ∈ Cc.val := by
    rw [hC]
    exact ⟨a, haC, rfl⟩
  obtain ⟨b, hb⟩ := (B.range_translatedApartmentMap h).ge (hCsub hpoint)
  change h • B.apartmentMap b = g • B.apartmentMap a at hb
  have hab : (h⁻¹ * g) • B.apartmentMap a = B.apartmentMap b := by
    rw [mul_smul, ← hb, inv_smul_smul]
  obtain ⟨n, _, heq⟩ := B.exists_normalizer_eq_on_translated_facetClosure hD (h⁻¹ * g) hab
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
  refine ⟨n • Fa, n • Ca, B.normalizer_smul_isFaceOf hD hAff n,
    hF.trans (himage Fa hFa), hC.trans (himage Ca ?_)⟩
  rw [← ha]
  exact AffineRootSystem.facet_subset_facetClosure _ _

/-- A chart image is contained in its translated apartment. -/
theorem translatedApartmentMap_image_subset (h : rationalPoints G) (Fa : Set B.Apartment) :
    B.translatedApartmentMap h '' Fa ⊆ h • B.apartmentImage := by
  rintro _ ⟨a, _, rfl⟩
  exact (B.range_translatedApartmentMap h).le ⟨a, rfl⟩

/-- With injective apartment charts, incidence in any fixed common chart is
exactly affine face incidence. -/
theorem facetPrecedes_iff_isFaceOf
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    {Fc Cc : BuildingFacet B} (h : rationalPoints G) {Fa Ca : Set B.Apartment}
    (hF : Fc.val = B.translatedApartmentMap h '' Fa)
    (hC : Cc.val = B.translatedApartmentMap h '' Ca) :
    FacetPrecedes B Fc Cc ↔ AffineRootSystem.IsFaceOf B.affineRoots Fa Ca := by
  constructor
  · intro hFC
    obtain ⟨Fa', Ca', hAff, hF', hC'⟩ :=
      B.exists_apartment_faces_of_facetPrecedes hD hFC h
        (hC ▸ B.translatedApartmentMap_image_subset h Ca)
    have hFa : Fa' = Fa :=
      (B.translatedApartmentMap_injective hinj h).image_injective (hF'.symm.trans hF)
    have hCa : Ca' = Ca :=
      (B.translatedApartmentMap_injective hinj h).image_injective (hC'.symm.trans hC)
    rwa [hFa, hCa] at hAff
  · intro hAff
    exact ⟨h, Fa, Ca, hAff, hF, hC⟩

/-- A face is contained in every translated apartment containing its upper facet. -/
theorem subset_apartment_of_facetPrecedes
    (hD : B.SatisfiesApartmentAxioms)
    {Fc Cc : BuildingFacet B} (hFC : FacetPrecedes B Fc Cc)
    (h : rationalPoints G) (hCsub : Cc.val ⊆ h • B.apartmentImage) :
    Fc.val ⊆ h • B.apartmentImage := by
  obtain ⟨Fa, _, _, hF, _⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hD hFC h hCsub
  rw [hF]
  exact B.translatedApartmentMap_image_subset h Fa

/-- The original incidence relation is transitive under the apartment axioms
and injectivity of the original apartment map. -/
theorem facetPrecedes_trans
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    {Fc Cc Dc : BuildingFacet B}
    (hFC : FacetPrecedes B Fc Cc) (hCD : FacetPrecedes B Cc Dc) :
    FacetPrecedes B Fc Dc := by
  obtain ⟨h, Da, _, hDchart⟩ := Dc.property
  have hDsub : Dc.val ⊆ h • B.apartmentImage := by
    rw [hDchart]
    exact B.translatedApartmentMap_image_subset h Da
  obtain ⟨Ca, Da', hCDa, hC, hD'⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hD hCD h hDsub
  have hCsub : Cc.val ⊆ h • B.apartmentImage := by
    rw [hC]
    exact B.translatedApartmentMap_image_subset h Ca
  obtain ⟨Fa, Ca', hFCa, hF, hC'⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hD hFC h hCsub
  have hCa : Ca' = Ca :=
    (B.translatedApartmentMap_injective hinj h).image_injective (hC'.symm.trans hC)
  rw [hCa] at hFCa
  exact ⟨h, Fa, Da', hFCa.trans hCDa, hF, hD'⟩

/-- Mutual incidence identifies the original building facets. -/
theorem facetPrecedes_antisymm
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    {Fc Cc : BuildingFacet B}
    (hFC : FacetPrecedes B Fc Cc) (hCF : FacetPrecedes B Cc Fc) : Fc = Cc := by
  obtain ⟨h, Ca, _, hCchart⟩ := Cc.property
  have hCsub : Cc.val ⊆ h • B.apartmentImage := by
    rw [hCchart]
    exact B.translatedApartmentMap_image_subset h Ca
  obtain ⟨Fa, Ca', hFCa, hF, hC⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hD hFC h hCsub
  have hCFa := (B.facetPrecedes_iff_isFaceOf hD hinj h hC hF).mp hCF
  apply Subtype.ext
  exact hF.trans ((congrArg (B.translatedApartmentMap h '' ·)
    (hFCa.antisymm hCFa)).trans hC.symm)

/-- A partial order on the existing building facets, with exactly the existing
face-incidence predicate as its order relation. -/
@[instance_reducible]
def buildingFacetPartialOrder
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap) :
    PartialOrder (BuildingFacet B) where
  le := FacetPrecedes B
  lt := fun Fc Cc => FacetPrecedes B Fc Cc ∧ ¬ FacetPrecedes B Cc Fc
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_refl := facetPrecedes_refl B
  le_trans := fun _ _ _ => B.facetPrecedes_trans hD hinj
  le_antisymm := fun _ _ => B.facetPrecedes_antisymm hD hinj

/-- Under actual opposite-factor pairs the apartment injection used by the
facet order follows from the full apartment axioms. -/
@[instance_reducible]
def buildingFacetPartialOrderOfRankOne
    (hD : B.SatisfiesApartmentAxioms)
    (hrank : RelativeRoot.HasRankOneFactorization B.i) : PartialOrder (BuildingFacet B) :=
  B.buildingFacetPartialOrder hD (B.apartmentMap_injective_of_rankOne hD hrank)

end ValuationBuildingData
end Langlands.Geometry.Building
