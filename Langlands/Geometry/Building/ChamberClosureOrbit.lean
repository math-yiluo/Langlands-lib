import Langlands.Geometry.Building.LangChamberReduction
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # Chambers through a point form a nonempty fixer orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- Every point has a chamber with the exact affine closure presentation. -/
theorem exists_chamberClosurePresentation (y : B.ReducedBuilding) :
    ∃ Y : Set B.ReducedBuilding, B.HasChamberClosurePresentation Y y := by
  obtain ⟨g, x, hx⟩ := B.exists_smul_apartmentMap y
  obtain ⟨x₀, hregular, hclosure⟩ :=
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
      B.hasOppositeFactorPairs).exists_regularPoint_closure x
  exact ⟨_, g, x₀, x, hregular, rfl, hclosure, hx⟩

/-- Two regular facets incident to the same apartment point are related by an
actual normalizer element fixing that point. -/
theorem exists_normalizer_fixing_facet
    {p x₀ x₁ : B.Apartment}
    (h₀ : AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots x₀)
    (h₁ : AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots x₁)
    (hp₀ : p ∈ AffineRootSystem.facetClosure B.affineRoots x₀)
    (hp₁ : p ∈ AffineRootSystem.facetClosure B.affineRoots x₁) :
    ∃ m : normalizerPoints B.i, m • p = p ∧
      (m • ·) '' AffineRootSystem.facet B.affineRoots x₀ =
        AffineRootSystem.facet B.affineRoots x₁ := by
  obtain ⟨w, hwp, hwrel⟩ := AffineRootSystem.exists_facetRel_fixing
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
      B.hasOppositeFactorPairs) h₀ h₁ hp₀ hp₁
  obtain ⟨m, hm⟩ := B.affineWeylGroup_le_range w.property
  refine ⟨m, ?_, ?_⟩
  · change B.apartment.normalizerAffineEquiv m p = p
    rw [hm]
    exact hwp
  · change (B.apartment.normalizerAffineEquiv m : B.Apartment → B.Apartment) ''
      AffineRootSystem.facet B.affineRoots x₀ =
        AffineRootSystem.facet B.affineRoots x₁
    rw [AffineRootSystem.image_facet
      (B.apartment.normalizerAffineEquiv_mem_rootStabilizer m)]
    apply AffineRootSystem.facet_eq_facet_iff.mpr
    change AffineRootSystem.facetRel B.affineRoots
      (B.apartment.normalizerAffineEquiv m x₀) x₁
    rw [hm]
    exact hwrel

/-- The full point fixer is transitive on chambers with a closure presentation
through that point. This does not assert transitivity of a smaller parahoric. -/
theorem exists_fixer_smul_chamber_eq
    {y : B.ReducedBuilding} {Y₀ Y₁ : Set B.ReducedBuilding}
    (hY₀ : B.HasChamberClosurePresentation Y₀ y)
    (hY₁ : B.HasChamberClosurePresentation Y₁ y) :
    ∃ g ∈ B.fixer y, (g • ·) '' Y₀ = Y₁ := by
  obtain ⟨g₀, x₀, a₀, h₀, rfl, ha₀, hy₀⟩ := hY₀
  obtain ⟨g₁, x₁, a₁, h₁, rfl, ha₁, hy₁⟩ := hY₁
  have heq : (g₀⁻¹ * g₁) • B.apartmentMap a₁ = B.apartmentMap a₀ := by
    rw [mul_smul, hy₁, ← hy₀, inv_smul_smul]
  have heq' :
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (g₀⁻¹ * g₁, a₁) =
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, a₀) := by
    have h :
        ApartmentQuotient.mk B.apartment.sharpFixerFamily ((g₀⁻¹ * g₁) * 1, a₁) =
          ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, a₀) := heq
    simpa only [mul_one] using h
  obtain ⟨n, hna, _⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily
      (g₀⁻¹ * g₁) 1 a₁ a₀).mp heq'
  have hnroot := B.apartment.normalizerAffineEquiv_mem_rootStabilizer n
  have hnregular :
      AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots (n • x₁) :=
    AffineRootSystem.GalleryGeometry.IsRegular.apply hnroot h₁
  have hnclosure : a₀ ∈ AffineRootSystem.facetClosure B.affineRoots (n • x₁) := by
    rw [← hna]
    exact (AffineRootSystem.mem_facetClosure_apply_iff hnroot a₁ x₁).mpr ha₁
  obtain ⟨m, hmfix, hmimage⟩ :=
    B.exists_normalizer_fixing_facet h₀ hnregular ha₀ hnclosure
  let g := g₁ * (n : rationalPoints G)⁻¹ * (m : rationalPoints G) * g₀⁻¹
  have hbase : g₀⁻¹ • y = B.apartmentMap a₀ := by
    rw [← hy₀, inv_smul_smul]
  refine ⟨g, B.mem_fixer.mpr ?_, ?_⟩
  · change (g₁ * (n : rationalPoints G)⁻¹ * (m : rationalPoints G) * g₀⁻¹) • y = y
    simp only [mul_smul, hbase]
    rw [B.normalizer_smul_apartmentMap, hmfix, ← hna,
      ← B.normalizer_smul_apartmentMap, inv_smul_smul, hy₁]
  · rw [Set.image_image]
    calc
      (fun x => g • (g₀ • B.apartmentMap x)) ''
          AffineRootSystem.facet B.affineRoots x₀ =
        (fun x => g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap x)) ''
          ((m • ·) '' AffineRootSystem.facet B.affineRoots x₀) := by
            rw [Set.image_image]
            congr 1
            funext x
            rw [← B.normalizer_smul_apartmentMap]
            simp only [g, mul_smul, inv_smul_smul]
      _ = (fun x => g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap x)) ''
          AffineRootSystem.facet B.affineRoots (n • x₁) := by rw [hmimage]
      _ = (fun x => g₁ • B.apartmentMap x) ''
          AffineRootSystem.facet B.affineRoots x₁ := by
            change (fun x => g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap x)) ''
                AffineRootSystem.facet B.affineRoots
                  (B.apartment.normalizerAffineEquiv n x₁) = _
            rw [← AffineRootSystem.image_facet hnroot x₁, Set.image_image]
            congr 1
            funext x
            change g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap (n • x)) =
              g₁ • B.apartmentMap x
            rw [← B.normalizer_smul_apartmentMap, inv_smul_smul]

end IntegerValuationBuildingData

/-- Existence and full-fixer transitivity for the exact chamber-closure
presentation over every supplied integer-valued building. -/
def IntegerValuationChamberClosureOrbitStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G) (y : B.ReducedBuilding),
    (∃ Y : Set B.ReducedBuilding, B.HasChamberClosurePresentation Y y) ∧
    (∀ Y₀ Y₁ : Set B.ReducedBuilding,
      B.HasChamberClosurePresentation Y₀ y →
      B.HasChamberClosurePresentation Y₁ y →
      ∃ g ∈ B.fixer y, (g • ·) '' Y₀ = Y₁)

/-- The chamber-closure orbit statement is proved without extra building axioms. -/
theorem integerValuationChamberClosureOrbit :
    IntegerValuationChamberClosureOrbitStatement.{u} := by
  intro k _ v G _ B y
  exact ⟨B.exists_chamberClosurePresentation y,
    fun _ _ h₀ h₁ => B.exists_fixer_smul_chamber_eq h₀ h₁⟩

end Langlands.Geometry.Building
