import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.Geometry.Building.CrossTorusAffineRoots
import Langlands.Geometry.Building.AffineFacetTransport
import Langlands.Geometry.Building.AffineRootSystemTransport

/-! # Actual geometric witnesses under ambient isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Affine
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace AffineRootSystem

section Affine

variable {V A W C : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  [AddCommGroup W] [Module ℝ W] [AddTorsor W C]

/-- Parallelism is preserved by an affine equivalence between different spaces. -/
theorem parallel_map_crossAffineEquiv {s₁ s₂ : AffineSubspace ℝ A}
    (h : s₁ ∥ s₂) (e : A ≃ᵃ[ℝ] C) :
    s₁.map e.toAffineMap ∥ s₂.map e.toAffineMap := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨e.linear v, ?_⟩
  rw [AffineSubspace.map_map, AffineSubspace.map_map]
  congr 1
  ext x
  simp [AffineEquiv.map_vadd]

/-- A singleton facet is preserved and reflected by full affine-root transport. -/
theorem isVertex_transportedRoots_iff (e : A ≃ᵃ[ℝ] C)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    IsVertex (transportedRoots e Ψ) (e x) ↔ IsVertex Ψ x := by
  change facet (transportedRoots e Ψ) (e x) = {e x} ↔ facet Ψ x = {x}
  rw [← image_facet_transportedRoots, ← Set.image_singleton]
  exact e.injective.image_injective.eq_iff

/-- Parallel vanishing root hyperplanes transport without root-system axioms. -/
theorem IsSpecialPoint.transport {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x : A}
    (hx : IsSpecialPoint Ψ x) (e : A ≃ᵃ[ℝ] C) :
    IsSpecialPoint (transportedRoots e Ψ) (e x) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', hparallel⟩ := hx ψ hψ
  refine ⟨affineFunctionalTransport e ψ',
    ⟨⟨ψ', hψ'.1, rfl⟩, ?_⟩, ?_⟩
  · simpa only [affineFunctionalTransport_apply, AffineEquiv.symm_apply_apply] using hψ'.2
  · rw [hyperplane_affineFunctionalTransport, hyperplane_affineFunctionalTransport]
    exact parallel_map_crossAffineEquiv hparallel e

/-- Specialness is preserved and reflected by the same full root comparison. -/
theorem isSpecialPoint_transportedRoots_iff (e : A ≃ᵃ[ℝ] C)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    IsSpecialPoint (transportedRoots e Ψ) (e x) ↔ IsSpecialPoint Ψ x := by
  constructor
  · intro hx
    simpa only [transportedRoots_symm, AffineEquiv.symm_apply_apply] using hx.transport e.symm
  · exact fun hx => hx.transport e

end Affine
end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

omit [IsAffineHom H.X.hom] in
private theorem identitySquare (B : ValuationBuildingData G) (f : G ≅ H) :
    B.i ≫ f.hom =
      CommGroupScheme.groupHom (CategoryTheory.Iso.refl B.S).hom ≫ (B.i ≫ f.hom) := by
  change B.i ≫ f.hom = 𝟙 _ ≫ (B.i ≫ f.hom)
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem pointMap_bijective (f : G ≅ H) :
    Function.Bijective (rationalPoints.map f.hom) :=
  (isoPointsEquiv f (Over.mk (𝟙 _))).bijective

private instance mappedMono (B : ValuationBuildingData G) (f : G ≅ H) :
    Mono (B.i ≫ f.hom).hom.hom.left :=
  mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)

/-- The actual affine comparison of the source and transported valuation apartments. -/
def mapIsoApartmentAffineEquiv (B : ValuationBuildingData G) (f : G ≅ H) :
    B.Apartment ≃ᵃ[ℝ] (B.mapIso f).Apartment :=
  B.apartment.apartmentTransportAffineEquiv (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identitySquare B f)

/-- The apartment comparison and the quotient comparison commute on the original chart. -/
@[simp] theorem mapIsoReducedBuildingEquiv_apartmentMap
    (B : ValuationBuildingData G) (f : G ≅ H) (x : B.Apartment) :
    B.mapIsoReducedBuildingEquiv f (B.apartmentMap x) =
      (B.mapIso f).apartmentMap (B.mapIsoApartmentAffineEquiv f x) :=
  B.apartment.reducedBuildingTransportEquiv_apartmentMap (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identitySquare B f) x

/-- The ordinary affine-root sets are equal through the actual apartment comparison. -/
theorem mapIso_transported_affineRoots (B : ValuationBuildingData G) (f : G ≅ H) :
    AffineRootSystem.transportedRoots (B.mapIsoApartmentAffineEquiv f) B.affineRoots =
      (B.mapIso f).affineRoots := by
  have hfunc (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
      AffineRootSystem.affineFunctionalTransport (B.mapIsoApartmentAffineEquiv f) ψ =
        B.apartment.affineFunctionalTransportEquiv (j := B.i ≫ f.hom)
          (CategoryTheory.Iso.refl B.S) f (identitySquare B f) ψ := by
    ext x
    rfl
  ext ψ'
  obtain ⟨ψ, rfl⟩ :=
    (AffineRootSystem.affineFunctionalTransport (B.mapIsoApartmentAffineEquiv f)).surjective ψ'
  constructor
  · rintro ⟨ζ, hζ, hζψ⟩
    have hζeq :=
      (AffineRootSystem.affineFunctionalTransport (B.mapIsoApartmentAffineEquiv f)).injective hζψ
    subst ζ
    rw [hfunc]
    exact (B.apartment.mem_affineRoots_transport_iff (j := B.i ≫ f.hom)
      (CategoryTheory.Iso.refl B.S) f (identitySquare B f) ψ).mpr hζ
  · intro hψ
    rw [hfunc] at hψ
    exact ⟨ψ, (B.apartment.mem_affineRoots_transport_iff (j := B.i ≫ f.hom)
      (CategoryTheory.Iso.refl B.S) f (identitySquare B f) ψ).mp hψ, rfl⟩

/-- The original full quotient equivalence preserves and reflects vertices. -/
theorem isVertex_mapIso_iff (B : ValuationBuildingData G) (f : G ≅ H)
    (x : B.ReducedBuilding) :
    (B.mapIso f).IsVertex (B.mapIsoReducedBuildingEquiv f x) ↔ B.IsVertex x := by
  have hvertex (a : B.Apartment) :
      AffineRootSystem.IsVertex (B.mapIso f).affineRoots (B.mapIsoApartmentAffineEquiv f a) ↔
        AffineRootSystem.IsVertex B.affineRoots a := by
    rw [← B.mapIso_transported_affineRoots f]
    exact AffineRootSystem.isVertex_transportedRoots_iff _ _ _
  constructor
  · rintro ⟨g, a, heq, ha⟩
    obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective g
    obtain ⟨a, rfl⟩ := (B.mapIsoApartmentAffineEquiv f).surjective a
    refine ⟨g, a, (B.mapIsoReducedBuildingEquiv f).injective ?_, (hvertex a).mp ha⟩
    rw [B.mapIsoReducedBuildingEquiv_smul, B.mapIsoReducedBuildingEquiv_apartmentMap]
    exact heq
  · rintro ⟨g, a, rfl, ha⟩
    exact ⟨rationalPoints.map f.hom g, B.mapIsoApartmentAffineEquiv f a,
      by rw [B.mapIsoReducedBuildingEquiv_smul, B.mapIsoReducedBuildingEquiv_apartmentMap],
      (hvertex a).mpr ha⟩

/-- The same equivalence preserves and reflects special points in translated apartments. -/
theorem isSpecialPoint_mapIso_iff (B : ValuationBuildingData G) (f : G ≅ H)
    (x : B.ReducedBuilding) :
    (B.mapIso f).IsSpecialPoint (B.mapIsoReducedBuildingEquiv f x) ↔ B.IsSpecialPoint x := by
  have hspecial (a : B.Apartment) :
      AffineRootSystem.IsSpecialPoint (B.mapIso f).affineRoots (B.mapIsoApartmentAffineEquiv f a) ↔
        AffineRootSystem.IsSpecialPoint B.affineRoots a := by
    rw [← B.mapIso_transported_affineRoots f]
    exact AffineRootSystem.isSpecialPoint_transportedRoots_iff _ _ _
  constructor
  · rintro ⟨g, a, heq, ha⟩
    obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective g
    obtain ⟨a, rfl⟩ := (B.mapIsoApartmentAffineEquiv f).surjective a
    refine ⟨g, a, (B.mapIsoReducedBuildingEquiv f).injective ?_, (hspecial a).mp ha⟩
    rw [B.mapIsoReducedBuildingEquiv_smul, B.mapIsoReducedBuildingEquiv_apartmentMap]
    exact heq
  · rintro ⟨g, a, rfl, ha⟩
    exact ⟨rationalPoints.map f.hom g, B.mapIsoApartmentAffineEquiv f a,
      by rw [B.mapIsoReducedBuildingEquiv_smul, B.mapIsoReducedBuildingEquiv_apartmentMap],
      (hspecial a).mpr ha⟩

end ValuationBuildingData
end Langlands.Geometry.Building
