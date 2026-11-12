import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreRestrictionTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProductFinitePresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness

/-! # An actual space over its represented target scheme -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Recover an original chart from its forgetful restriction. -/
theorem originalBaseChart_forgetBaseYoneda_comp {T : Scheme.{u}} (g : T ⟶ S)
    (U : Over T) {F : Presheaf S}
    (a : (schemeYoneda S).obj ((Over.map g).obj U) ⟶ F) :
    originalBaseChart g (forgetBaseYoneda g U ≫ (restrictPresheaf g).map a) = a := by
  apply forgetBaseYoneda_comp_injective g U
  exact originalBaseChart_restrict g _

namespace SchemeTargetRebase

variable (V : Over S)

/-- The base itself, with its original structure map recovered. -/
def originalBaseIso :
    (Over.map V.hom).obj (Over.mk (𝟙 V.left)) ≅ V :=
  Over.isoMk (Iso.refl _) (by simp)

/-- The canonical section of the base-changed represented target. -/
def sectionMap :
    (schemeYoneda V.left).obj (Over.mk (𝟙 V.left)) ⟶
      (restrictPresheaf V.hom).obj ((schemeYoneda S).obj V) :=
  forgetBaseYoneda V.hom (Over.mk (𝟙 V.left)) ≫
    (restrictPresheaf V.hom).map ((schemeYoneda S).map (originalBaseIso V).hom)

@[simp]
theorem originalBaseChart_sectionMap :
    originalBaseChart V.hom (sectionMap V) = (schemeYoneda S).map (originalBaseIso V).hom :=
  originalBaseChart_forgetBaseYoneda_comp V.hom _ _

/-- The canonical section as an actual morphism of algebraic spaces. -/
def sectionMorphism :
    (schemeToSpace V.left).obj (Over.mk (𝟙 V.left)) ⟶
      baseChange V.hom ((schemeToSpace S).obj V) :=
  homMk (sectionMap V)

variable {V} {X : AlgebraicSpace S} (f : X ⟶ (schemeToSpace S).obj V)

/-- The actual algebraic space over the represented target scheme. -/
def space : AlgebraicSpace V.left :=
  fibreProduct (baseChangeMap V.hom f) (sectionMorphism V)

/-- Before restricting its scheme base, the auxiliary fibre is the original space. -/
def originalFibreIso :
    X.presheaf ≅ Limits.pullback (hom f) (originalBaseChart V.hom (sectionMap V)) := by
  rw [originalBaseChart_sectionMap]
  exact (IsPullback.of_horiz_isIso
    (fst := 𝟙 X.presheaf)
    (snd := hom f ≫ (schemeYoneda S).map (originalBaseIso V).inv)
    (f := hom f) (g := (schemeYoneda S).map (originalBaseIso V).hom)
    ⟨by
      rw [Category.id_comp, Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id, (schemeYoneda S).map_id V]
      exact (Category.comp_id (hom f)).symm⟩).isoPullback

/-- Recover an atlas over the new scheme base from an atlas of the original space. -/
def atlasData {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) :
    FibreRestrictionAtlas V.hom (hom f) (sectionMap V) :=
  FibreRestrictionAtlas.of_original V.hom (hom f) (sectionMap V)
    (a ≫ (originalFibreIso f).hom)
    (ha.comp_iso (originalFibreIso f)) (hs.comp_iso (originalFibreIso f))

/-- The atlas has exactly the same underlying scheme. -/
theorem atlasData_source_left {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) :
    (atlasData f a ha hs).source.left = U.left := rfl

/-- Its new structure map recovers the original structure map after composition. -/
theorem atlasData_source_hom_comp {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) :
    (atlasData f a ha hs).source.hom ≫ V.hom = U.hom := by
  let p : U ⟶ (Over.map V.hom).obj (Over.mk (𝟙 V.left)) :=
    (schemeYoneda S).preimage
      ((a ≫ (originalFibreIso f).hom) ≫
        Limits.pullback.snd (hom f) (originalBaseChart V.hom (sectionMap V)))
  change (p.left ≫ 𝟙 V.left) ≫ V.hom = U.hom
  simpa only [Category.assoc, Category.comp_id, Category.id_comp,
    Over.map_obj_hom, Over.mk_hom] using
    Over.w p

/-- The rebased atlas map into the actual space. -/
def atlas {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) :
    (schemeYoneda V.left).obj (atlasData f a ha hs).source ⟶ (space f).presheaf :=
  (atlasData f a ha hs).map ≫
    (FibreProduct.presheafIso (baseChangeMap V.hom f) (sectionMorphism V)).inv

theorem atlas_isEtale {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) : IsEtale (atlas f a ha hs) :=
  (atlasData f a ha hs).etale.comp_iso
    (FibreProduct.presheafIso (baseChangeMap V.hom f) (sectionMorphism V)).symm

theorem atlas_isSurjective {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) : IsSurjective (atlas f a ha hs) :=
  (atlasData f a ha hs).surjective.comp_iso
    (FibreProduct.presheafIso (baseChangeMap V.hom f) (sectionMorphism V)).symm

/-- Relative quasi-separatedness is preserved by this construction. -/
theorem isQuasiSeparated (hX : IsQuasiSeparated X) : IsQuasiSeparated (space f) := by
  have : QuasiSeparated (Over.mk (𝟙 V.left)).hom := by
    change QuasiSeparated (𝟙 V.left)
    infer_instance
  exact FibreProduct.isQuasiSeparated _ _ (hX.baseChange (g := V.hom))
    (isQuasiSeparated_schemeToSpace (Over.mk (𝟙 V.left)))

/-- Finite-presentation atlas data remain finite-presentation atlas data over an
affine represented target locally of finite type over the original affine base. -/
theorem hasAtlasProperty_finitePresentation [IsAffine S] [IsAffine V.left]
    [LocallyOfFiniteType V.hom]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) (space f) := by
  obtain ⟨U, a, ha, hs, hUl, hUq⟩ := hX
  let := hUl
  let := hUq
  let A := atlasData f a ha hs
  have : LocallyOfFinitePresentation (A.source.hom ≫ V.hom) := by
    rw [atlasData_source_hom_comp]
    infer_instance
  have hl : LocallyOfFinitePresentation A.source.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp _ V.hom
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  have : CompactSpace A.source.left := by
    change CompactSpace U.left
    infer_instance
  exact ⟨A.source, atlas f a ha hs, atlas_isEtale f a ha hs,
    atlas_isSurjective f a ha hs, hl, inferInstance⟩

end SchemeTargetRebase

end Langlands.AlgebraicGeometry.AlgebraicSpace
