import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.Geometry.Building.CrossTorusReducedBuilding
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Actual building data and quotient transport under ambient isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem identityTorusSquare (i : S.toGrp ⟶ G) (f : G ≅ H) :
    i ≫ f.hom =
      CommGroupScheme.groupHom (CategoryTheory.Iso.refl S).hom ≫ (i ≫ f.hom) := by
  change i ≫ f.hom = 𝟙 _ ≫ (i ≫ f.hom)
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem pointMap_bijective (f : G ≅ H) :
    Function.Bijective (rationalPoints.map f.hom) :=
  (isoPointsEquiv f (Over.mk (𝟙 _))).bijective

/-- The actual centralizer keeps its source and torus factorization and changes
its ambient inclusion by the given group-scheme isomorphism. -/
def CentralizerDatum.mapIso (C : CentralizerDatum i) (f : G ≅ H) :
    CentralizerDatum (i ≫ f.hom) where
  Z := C.Z
  j := C.j ≫ f.hom
  s := C.s
  isClosedSubgroup := C.isClosedSubgroup.comp_iso f
  isRepresentedBy := C.isRepresentedBy.torusCentralizer_of_iso_square
    (CategoryTheory.Iso.refl S.toGrp) f (by simp)
  comp_eq := by rw [← Category.assoc, C.comp_eq]
  bijective := C.bijective

section Compatibility

variable [Mono i.hom.hom.left] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (C : CentralizerDatum i) (f : G ≅ H)

private instance mappedTorusMono : Mono (i ≫ f.hom).hom.hom.left := by
  change Mono (i.hom.hom.left ≫ f.hom.hom.hom.left)
  infer_instance

omit [Mono i.hom.hom.left] in
/-- With the same torus and centralizer source, ambient transport preserves the
full V6 equation at every original centralizer point. -/
theorem IsCentralizerCompatible.mapIso {φ : RootFunctionFamily S G}
    (hφ : IsCentralizerCompatible i C.j C.s C.bijective φ) :
    IsCentralizerCompatible (i ≫ f.hom) (C.mapIso f).j
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

/-- The whole transported valuation class satisfies V6 for the transported
representative of the actual centralizer. -/
theorem KPApartmentData.IsOmegaCompatible.mapIso
    {D : KPApartmentData i (localFieldOrder F)} (hD : D.IsOmegaCompatible C) :
    (D.transport (CategoryTheory.Iso.refl S) f (identityTorusSquare i f)).IsOmegaCompatible
      (C.mapIso f) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact (hD φ hφ).mapIso C f

end Compatibility

namespace ValuationBuildingData

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Carry actual valuation-building data through an ambient group-scheme
isomorphism, retaining its torus and centralizer sources. -/
def mapIso (B : ValuationBuildingData G) (f : G ≅ H) : ValuationBuildingData H where
  isConnectedReductive := B.isConnectedReductive.of_iso f.symm
  S := B.S
  i := B.i ≫ f.hom
  isMaximalSplitTorus := B.isMaximalSplitTorus.comp_iso f
  apartment := B.apartment.transport (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f)
  centralizer := B.centralizer.mapIso f
  isOmegaCompatible := B.isOmegaCompatible.mapIso B.centralizer f

/-- The target is the actual transported inclusion of the original torus. -/
@[simp] theorem mapIso_i (B : ValuationBuildingData G) (f : G ≅ H) :
    (B.mapIso f).i = B.i ≫ f.hom := rfl

/-- The actual quotient equivalence transports both the rational-point and
the valuation-family coordinates of every representative. -/
def mapIsoReducedBuildingEquiv (B : ValuationBuildingData G) (f : G ≅ H) :
    B.ReducedBuilding ≃ (B.mapIso f).ReducedBuilding := by
  letI : Mono (B.i ≫ f.hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)
  exact B.apartment.reducedBuildingTransportEquiv (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f)

/-- The equivalence intertwines the original quotient actions through the
actual point map induced by the ambient isomorphism. -/
theorem mapIsoReducedBuildingEquiv_smul (B : ValuationBuildingData G) (f : G ≅ H)
    (g : rationalPoints G) (x : B.ReducedBuilding) :
    B.mapIsoReducedBuildingEquiv f (g • x) =
      rationalPoints.map f.hom g • B.mapIsoReducedBuildingEquiv f x := by
  have : Mono (B.i ≫ f.hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)
  exact B.apartment.reducedBuildingTransportEquiv_smul (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) g x

/-- Full point fixers have exactly the actual ambient subgroup images. -/
theorem map_fixer_mapIso (B : ValuationBuildingData G) (f : G ≅ H)
    (x : B.ReducedBuilding) :
    (B.fixer x).map (rationalPoints.map f.hom) =
      (B.mapIso f).fixer (B.mapIsoReducedBuildingEquiv f x) := by
  have : Mono (B.i ≫ f.hom).hom.hom.left :=
    mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus.comp_iso f)
  exact B.apartment.map_reducedFixer_transport (j := B.i ≫ f.hom)
    (CategoryTheory.Iso.refl B.S) f (identityTorusSquare B.i f) x

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The norm-one condition is preserved and reflected by the actual ambient
point map, using rational-character restriction in both directions. -/
theorem mem_rationalCommonNormKernel_mapIso_iff (f : G ≅ H) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈ rationalCommonNormKernel H ↔
      g ∈ rationalCommonNormKernel G := by
  constructor
  · intro hg
    have h := map_mem_rationalCommonNormKernel f.inv hg
    simpa only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using h
  · exact map_mem_rationalCommonNormKernel f.hom

/-- The norm-one point stabilizers, including the original common character
kernel, have exactly the actual ambient subgroup images. -/
theorem map_compactStabilizer_mapIso (B : ValuationBuildingData G) (f : G ≅ H)
    (x : B.ReducedBuilding) :
    (B.compactStabilizer x).map (rationalPoints.map f.hom) =
      (B.mapIso f).compactStabilizer (B.mapIsoReducedBuildingEquiv f x) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective y
  rw [Subgroup.mem_map_iff_mem (pointMap_bijective f).injective,
    B.mem_compactStabilizer, (B.mapIso f).mem_compactStabilizer,
    mem_rationalCommonNormKernel_mapIso_iff, ← B.mapIsoReducedBuildingEquiv_smul]
  exact and_congr_right fun _ => (B.mapIsoReducedBuildingEquiv f).injective.eq_iff.symm

end ValuationBuildingData

end Langlands.Geometry.Building
