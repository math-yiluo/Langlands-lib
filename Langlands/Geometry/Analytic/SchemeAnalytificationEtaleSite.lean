import Langlands.Geometry.Analytic.SchemeAnalytificationLocalizedFunctor
import Langlands.Geometry.Analytic.SchemeAnalytificationImage
import Langlands.Geometry.Analytic.LocalizedEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonStatement
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleProof
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Analytification on separated algebraic étale objects -/

noncomputable section

universe u w

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry
open SaturatedAtlasPresentation AffineAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Localized

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (f' : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [LocallyOfFiniteType f']

private theorem isOpen_chartDomain (U : X.affineOpens) :
    IsOpen (chartDomain K f U).carrier := by
  rw [chartDomain_carrier, OpenGluing.range_ι K f U]
  exact (OpenGluing.isOpenEmbedding_ι K f U).isOpen_range

private theorem chartDomain_eq_openDomain (U : X.affineOpens) :
    (model K f).openDomain (chartDomain K f U).carrier (isOpen_chartDomain K f U) =
      chartDomain K f U := by
  apply SetLike.coe_injective
  rfl

/-- The analytification of an affine open is an étale chart of the glued space. -/
theorem etale_chartInclusion (U : X.affineOpens) : etale (chartInclusion K f U) := by
  apply etale_comp (etale_of_isIso (chartIso K f U).hom)
  have h := etaleOpenDomainStatement (object K f) (chartDomain K f U).carrier
    (isOpen_chartDomain K f U)
  change etale ((model K f).localizedDomainInclusion
    ((model K f).openDomain (chartDomain K f U).carrier (isOpen_chartDomain K f U))) at h
  rwa [chartDomain_eq_openDomain] at h

/-- Étaleness of a map of separated schemes implies étaleness of the glued
analytification, given the affine all-pieces comparison in the small index universe. -/
theorem etale_map (hSmall : StrongEtaleSmallIndexComparisonStatement.{u})
    [IsSeparated f] [IsSeparated f'] (g : X ⟶ Y) [Etale g] (hg : g ≫ f' = f) :
    etale (map K f f' g hg) := by
  let D (p : AffinePair g) := (chartDomain K f p.source).carrier
  refine etale_of_open_source_cover (map K f f' g hg) D
    (fun p => isOpen_chartDomain K f p.source) ?_ ?_
  · intro z
    obtain ⟨U, V, h, y, rfl⟩ :=
      MorphismCompatibility.exists_subordinate_chart K f (OpenGluing.range_ι K f) g z
    refine ⟨⟨U, V, h⟩, ?_⟩
    change ι K f U y ∈ (chartDomain K f U).carrier
    rw [chartDomain_carrier, OpenGluing.range_ι K f U]
    exact ⟨y, rfl⟩
  · intro p
    change etale ((model K f).localizedDomainInclusion
      ((model K f).openDomain (chartDomain K f p.source).carrier
        (isOpen_chartDomain K f p.source)) ≫ map K f f' g hg)
    rw [chartDomain_eq_openDomain]
    have hU : IsAffine (p.source : X.Opens).toScheme := p.source.property
    have hV : IsAffine (p.target : Y.Opens).toScheme := p.target.property
    have hCoord : (openCoordinateMap g hg p.le_preimage).toRingHom.Etale :=
      HasRingHomProperty.appTop (@Etale) _ (inferInstance :
        Etale (g.resLE (p.target : Y.Opens) (p.source : X.Opens) p.le_preimage))
    have ha : etale (affineMap K f f' g hg p.le_preimage) :=
      affineAnalytificationLocalizedEtaleReduction affineAnalytificationEtale hSmall K _ _
        (chartPresentation K f' p.target) (chartPresentation K f p.source)
        (openCoordinateMap g hg p.le_preimage) hCoord
    have he := etale_comp (etale_of_isIso (chartIso K f p.source).inv)
      (etale_comp ha (etale_chartInclusion K f' p.target))
    rw [← chartInclusion_map K f f' g hg p.le_preimage, chartInclusion] at he
    rwa [Category.assoc ((chartIso K f p.source).hom), Iso.inv_hom_id_assoc] at he

end Localized

/-- Étaleness on the category of separated schemes locally of finite type over `K`. -/
abbrev separatedEtale : MorphismProperty (separatedLocallyFiniteTypeOver K).FullSubcategory :=
  (show MorphismProperty Scheme.{u} from @Etale).inverseImage
    ((separatedLocallyFiniteTypeOver K).ι ⋙ Over.forget _)

variable (X : (separatedLocallyFiniteTypeOver K).FullSubcategory)

/-- The category of algebraic étale objects with source separated over `K`. -/
abbrev SeparatedAlgebraicEtale := (separatedEtale K).Over ⊤ X

/-- The inclusion in the scheme's usual small algebraic étale category. -/
def separatedAlgebraicEtaleForget : SeparatedAlgebraicEtale K X ⥤ X.obj.left.Etale where
  obj U := MorphismProperty.Over.mk ⊤ U.hom.hom.left U.prop
  map g := MorphismProperty.Over.homMk g.left.hom.left
    (((separatedLocallyFiniteTypeOver K).ι ⋙ Over.forget _).congr_map
      (MorphismProperty.Over.w g))
  map_id _ := MorphismProperty.Over.Hom.ext rfl
  map_comp _ _ := MorphismProperty.Over.Hom.ext rfl

variable (hSmall : StrongEtaleSmallIndexComparisonStatement.{u})

/-- Analytification on étale objects over the analytification of the base scheme. -/
def separatedEtaleAnalytification :
    SeparatedAlgebraicEtale K X ⥤ EtaleSite ((localizedAnalytification K).obj X) where
  obj U := MorphismProperty.Over.mk ⊤ ((localizedAnalytification K).map U.hom) (by
    let : LocallyOfFiniteType U.left.obj.hom := U.left.property.1
    let : LocallyOfFiniteType X.obj.hom := X.property.1
    let : IsSeparated U.left.obj.hom := U.left.property.2
    let : IsSeparated X.obj.hom := X.property.2
    let : Etale U.hom.hom.left := U.prop
    exact Localized.etale_map K U.left.obj.hom X.obj.hom hSmall U.hom.hom.left (Over.w U.hom.hom))
  map {U V} g := MorphismProperty.Over.homMk ((localizedAnalytification K).map g.left) (by
    change (localizedAnalytification K).map g.left ≫ (localizedAnalytification K).map V.hom =
      (localizedAnalytification K).map U.hom
    rw [← Functor.map_comp, MorphismProperty.Over.w])
  map_id U := MorphismProperty.Over.Hom.ext ((localizedAnalytification K).map_id U.left)
  map_comp g k := MorphismProperty.Over.Hom.ext ((localizedAnalytification K).map_comp g.left k.left)

/-- An algebraic étale covering family with separated sources analytifies to a covering
family for the ordinary analytic étale topology. -/
theorem separatedEtaleAnalytification_cover {I : Type w} {U : SeparatedAlgebraicEtale K X}
    (V : I → SeparatedAlgebraicEtale K X) (a : ∀ i, V i ⟶ U)
    (h : Sieve.ofArrows (fun i => (separatedAlgebraicEtaleForget K X).obj (V i))
        (fun i => (separatedAlgebraicEtaleForget K X).map (a i)) ∈
      Scheme.smallEtaleTopology X.obj.left ((separatedAlgebraicEtaleForget K X).obj U)) :
    Sieve.ofArrows (fun i => (separatedEtaleAnalytification K X hSmall).obj (V i))
        (fun i => (separatedEtaleAnalytification K X hSmall).map (a i)) ∈
      etaleTopology ((localizedAnalytification K).obj X)
        ((separatedEtaleAnalytification K X hSmall).obj U) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at h
  refine generate_mem_etaleTopology (ofArrows_mem_etalePrecoverage_iff.mpr ?_)
  let : LocallyOfFiniteType U.left.obj.hom := U.left.property.1
  let : IsSeparated U.left.obj.hom := U.left.property.2
  intro z
  have hz : center K U.left.obj.hom z ∈
      ⋃ i, Set.range ((separatedAlgebraicEtaleForget K X).map (a i)).left := by
    rw [h]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  let : LocallyOfFiniteType (V i).left.obj.hom := (V i).left.property.1
  let : IsSeparated (V i).left.obj.hom := (V i).left.property.2
  use i
  change z ∈ Set.range ((localizedSpaceFunctor.map (Localized.map K (V i).left.obj.hom
    U.left.obj.hom (a i).left.hom.left (Over.w (a i).left.hom))).hom)
  rw [Localized.underlying_map]
  have hRange := range_analytification K (V i).left.obj.hom U.left.obj.hom
    (a i).left.hom.left (Over.w (a i).left.hom)
  exact hRange.symm ▸ hi

end Langlands.Analytic.SchemeAnalytification
