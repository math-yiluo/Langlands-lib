import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.ValuationBuildingIsoGeometry

/-! # Actual ambient transport for explicit integer-valued buildings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Affine
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G}
  {v : Valuation k (WithZero (Multiplicative ℤ))}

private theorem identityTorusSquare (i : S.toGrp ⟶ G) (f : G ≅ H) :
    i ≫ f.hom =
      CommGroupScheme.groupHom (CategoryTheory.Iso.refl S).hom ≫ (i ≫ f.hom) := by
  change i ≫ f.hom = 𝟙 _ ≫ (i ≫ f.hom)
  simp

private theorem pointMap_bijective (f : G ≅ H) :
    Function.Bijective (rationalPoints.map f.hom) :=
  (isoPointsEquiv f (Over.mk (𝟙 _))).bijective

section Compatibility

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (C : CentralizerDatum i) (f : G ≅ H)

/-- With the same torus and centralizer source, ambient transport preserves the
full V6 equation at every original centralizer point. -/
theorem IntegerValuation.IsCentralizerCompatible.mapIso {φ : RootFunctionFamily S G}
    (hφ : IntegerValuation.IsCentralizerCompatible v i C.j C.s C.bijective φ) :
    IntegerValuation.IsCentralizerCompatible v (i ≫ f.hom) (C.mapIso f).j
      (C.mapIso f).s (C.mapIso f).bijective
      (RootFunctionFamily.transportEquiv (CategoryTheory.Iso.refl S) f φ) := by
  intro a ha z v hv
  have hs := identityTorusSquare i f
  have hchar : ⇑(characterLattice.congr (CategoryTheory.Iso.refl S)) = id := by
    funext a
    exact Category.id_comp a
  have hroots : relativeRoots (i ≫ f.hom) = relativeRoots i := by
    simpa [hchar] using
      (relativeRoots_image_of_transport (CategoryTheory.Iso.refl S) f hs).symm
  have ha' : a ∈ relativeRoots i := by
    rwa [hroots] at ha
  obtain ⟨v, rfl⟩ := (pointMap_bijective f).surjective v
  have hv' : v ∈ rootGroupPoints i a := by
    apply (rootGroupPoints_transport_iff (CategoryTheory.Iso.refl S) f hs a v).mp
    simpa [characterLattice.congr_apply] using hv
  have hj : rationalPoints.map (C.mapIso f).j z =
      rationalPoints.map f.hom (rationalPoints.map C.j z) := by
    change z ≫ (C.j ≫ f.hom).hom.hom = (z ≫ C.j.hom.hom) ≫ f.hom.hom.hom
    exact (Category.assoc _ _ _).symm
  have hmap (w : rationalPoints G) :
      RootFunctionFamily.transportEquiv (CategoryTheory.Iso.refl S) f φ a
        (rationalPoints.map f.hom w) = φ a w := by
    simpa [characterLattice.congr_apply] using
      RootFunctionFamily.transportEquiv_apply_map (CategoryTheory.Iso.refl S) f φ a w
  rw [hj, ← map_inv, ← map_mul, ← map_mul, hmap, hmap]
  exact hφ a ha' z v hv'

variable [Mono i.hom.hom.left]

/-- The whole transported valuation class satisfies V6 for the transported
representative of the actual centralizer. -/
theorem IntegerValuation.IsOmegaCompatible.mapIso
    {D : KPApartmentData i (IntegerValuation.order v)} (hD : IntegerValuation.IsOmegaCompatible v D C) :
    IntegerValuation.IsOmegaCompatible v
      (D.transport (CategoryTheory.Iso.refl S) f (identityTorusSquare i f)) (C.mapIso f) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact (hD φ hφ).mapIso C f


end Compatibility

namespace IntegerValuationBuildingData

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

private instance mappedMono (B : IntegerValuationBuildingData v G) (f : G ≅ H) :
    Mono (B.i ≫ f.hom).hom.hom.left :=
  mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)

/-- Carry actual valuation-building data through an ambient group-scheme
isomorphism, retaining its torus and centralizer sources. -/
def mapIso (B : IntegerValuationBuildingData v G) (f : G ≅ H) : IntegerValuationBuildingData v H where
  isConnectedReductive := B.isConnectedReductive.of_iso f.symm
  S := B.S
  i := B.i ≫ f.hom
  isMaximalSplitTorus := B.isMaximalSplitTorus.comp_iso f
  apartment := B.apartment.transport (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f)
  centralizer := B.centralizer.mapIso f
  isOmegaCompatible := B.isOmegaCompatible.mapIso B.centralizer f

/-- The target is the actual transported inclusion of the original torus. -/
@[simp] theorem mapIso_i (B : IntegerValuationBuildingData v G) (f : G ≅ H) :
    (B.mapIso f).i = B.i ≫ f.hom := rfl

/-- The actual quotient equivalence transports both the rational-point and
the valuation-family coordinates of every representative. -/
def mapIsoReducedBuildingEquiv (B : IntegerValuationBuildingData v G) (f : G ≅ H) :
    B.ReducedBuilding ≃ (B.mapIso f).ReducedBuilding := by
  letI : Mono (B.i ≫ f.hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)
  exact B.apartment.reducedBuildingTransportEquiv (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f)

/-- The equivalence intertwines the original quotient actions through the
actual point map induced by the ambient isomorphism. -/
theorem mapIsoReducedBuildingEquiv_smul (B : IntegerValuationBuildingData v G) (f : G ≅ H)
    (g : rationalPoints G) (x : B.ReducedBuilding) :
    B.mapIsoReducedBuildingEquiv f (g • x) =
      rationalPoints.map f.hom g • B.mapIsoReducedBuildingEquiv f x := by
  have : Mono (B.i ≫ f.hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)
  exact B.apartment.reducedBuildingTransportEquiv_smul (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) g x

/-- Full point fixers have exactly the actual ambient subgroup images. -/
theorem map_fixer_mapIso (B : IntegerValuationBuildingData v G) (f : G ≅ H)
    (x : B.ReducedBuilding) :
    (B.fixer x).map (rationalPoints.map f.hom) =
      (B.mapIso f).fixer (B.mapIsoReducedBuildingEquiv f x) := by
  have : Mono (B.i ≫ f.hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)
  exact B.apartment.map_reducedFixer_transport (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) x

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The original rational-character unit condition is preserved and reflected. -/
theorem mem_characterValuationKernel_mapIso_iff (f : G ≅ H) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈ characterValuationKernel v H ↔
      g ∈ characterValuationKernel v G := by
  constructor
  · intro hg
    have h := IntegerValuation.map_mem_characterValuationKernel v f.inv hg
    simpa only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using h
  · exact IntegerValuation.map_mem_characterValuationKernel v f.hom

/-- The original one-group stabilizer maps onto the transported one-group stabilizer. -/
theorem map_oneStabilizer_mapIso (B : IntegerValuationBuildingData v G) (f : G ≅ H)
    (x : B.ReducedBuilding) :
    (B.oneStabilizer x).map (rationalPoints.map f.hom) =
      (B.mapIso f).oneStabilizer (B.mapIsoReducedBuildingEquiv f x) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective y
  rw [Subgroup.mem_map_iff_mem (pointMap_bijective f).injective,
    B.mem_oneStabilizer, (B.mapIso f).mem_oneStabilizer,
    mem_characterValuationKernel_mapIso_iff, ← B.mapIsoReducedBuildingEquiv_smul]
  exact and_congr_right fun _ => (B.mapIsoReducedBuildingEquiv f).injective.eq_iff.symm

/-- The actual affine comparison of the source and transported valuation apartments. -/
def mapIsoApartmentAffineEquiv (B : IntegerValuationBuildingData v G) (f : G ≅ H) :
    B.Apartment ≃ᵃ[ℝ] (B.mapIso f).Apartment :=
  B.apartment.apartmentTransportAffineEquiv (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f)

/-- The apartment comparison and the quotient comparison commute on the original chart. -/
@[simp] theorem mapIsoReducedBuildingEquiv_apartmentMap
    (B : IntegerValuationBuildingData v G) (f : G ≅ H) (x : B.Apartment) :
    B.mapIsoReducedBuildingEquiv f (B.apartmentMap x) =
      (B.mapIso f).apartmentMap (B.mapIsoApartmentAffineEquiv f x) :=
  B.apartment.reducedBuildingTransportEquiv_apartmentMap (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) x

/-- The ordinary affine-root sets are equal through the actual apartment comparison. -/
theorem mapIso_transported_affineRoots (B : IntegerValuationBuildingData v G) (f : G ≅ H) :
    AffineRootSystem.transportedRoots (B.mapIsoApartmentAffineEquiv f) B.affineRoots =
      (B.mapIso f).affineRoots := by
  have hfunc (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
      AffineRootSystem.affineFunctionalTransport (B.mapIsoApartmentAffineEquiv f) ψ =
        B.apartment.affineFunctionalTransportEquiv (j := B.i ≫ f.hom)
          (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) ψ := by
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
      (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) ψ).mpr hζ
  · intro hψ
    rw [hfunc] at hψ
    exact ⟨ψ, (B.apartment.mem_affineRoots_transport_iff (j := B.i ≫ f.hom)
      (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) ψ).mp hψ, rfl⟩

/-- The original full quotient equivalence preserves and reflects vertices. -/
theorem isVertex_mapIso_iff (B : IntegerValuationBuildingData v G) (f : G ≅ H)
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
theorem isSpecialPoint_mapIso_iff (B : IntegerValuationBuildingData v G) (f : G ≅ H)
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


end IntegerValuationBuildingData
end Langlands.Geometry.Building
