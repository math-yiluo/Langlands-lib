import Langlands.Geometry.Building.IntegerBuildingFacetPartition

/-! # Reducing chamber stabilizers to the original apartment normalizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- Every element of the original normalizer preserving an apartment chamber
fixes every point of that chamber. -/
def ChamberNormalizerFixing : Prop :=
  ∀ Ca : Set B.Apartment, AffineRootSystem.IsChamber B.affineRoots Ca →
    ∀ n : normalizerPoints B.i, n • Ca = Ca → ∀ x ∈ Ca, n • x = x

/-- A stabilizer of a translated full facet agrees there with a normalizer element
that stabilizes the original apartment facet. -/
theorem exists_normalizer_stabilizes_eq_on_translated_facet
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (h g : rationalPoints G)
    (hg : (g • ·) '' ((fun y => h • B.apartmentMap y) '' Fa) =
      (fun y => h • B.apartmentMap y) '' Fa) :
    ∃ n : normalizerPoints B.i, n • Fa = Fa ∧
      ∀ y ∈ Fa, g • (h • B.apartmentMap y) =
        h • B.apartmentMap (n • y) := by
  have hnonempty : Fa.Nonempty := by
    obtain ⟨a, rfl⟩ := hFa
    exact ⟨a, AffineRootSystem.mem_facet_self _ _⟩
  obtain ⟨a, ha⟩ := hnonempty
  have hga : g • (h • B.apartmentMap a) ∈
      (fun y => h • B.apartmentMap y) '' Fa := by
    rw [← hg]
    exact ⟨h • B.apartmentMap a, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨b, hb, hab⟩ := hga
  have hab' : (h⁻¹ * g * h) • B.apartmentMap a = B.apartmentMap b := by
    have H := congrArg (h⁻¹ • ·) hab
    simpa only [mul_smul, inv_smul_smul] using H.symm
  obtain ⟨n, hn, heq⟩ :=
    B.exists_normalizer_eq_on_translated_facet hFa ha (h⁻¹ * g * h) hab'
  have hnFa : n • Fa = Fa :=
    (B.normalizer_smul_isFacet hFa n).eq_of_mem_mem hFa
      (hn ▸ Set.smul_mem_smul_set ha) hb
  refine ⟨n, hnFa, fun y hy => ?_⟩
  have H := congrArg (h • ·) (heq y hy)
  simpa only [mul_smul, smul_inv_smul] using H

/-- Pointwise fixing by chamber-preserving normalizer elements implies pointwise
fixing by all chamber stabilizers in the actual reduced quotient. -/
theorem mem_pointwiseFixer_of_stabilizes_chamber_of_normalizer_fixing
    (hN : B.ChamberNormalizerFixing)
    {Y : Set B.ReducedBuilding} (hY : B.IsChamber Y)
    (g : rationalPoints G) (hg : (g • ·) '' Y = Y) :
    g ∈ B.pointwiseFixer Y := by
  obtain ⟨h, Ca, hCa, rfl⟩ := hY
  obtain ⟨n, hn, heq⟩ :=
    B.exists_normalizer_stabilizes_eq_on_translated_facet hCa.isFacet h g hg
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer]
  rintro z ⟨x, hx, rfl⟩
  rw [heq x hx, hN Ca hCa n hn x hx]

end Langlands.Geometry.Building.IntegerValuationBuildingData
