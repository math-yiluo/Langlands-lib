import Langlands.Geometry.Analytic.LocalizedDomainGluing
import Langlands.Geometry.Analytic.SchemeAnalytificationAnalyticStructureProof
import Langlands.Geometry.Analytic.SchemeAnalytificationTopologicalFunctor
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.SpaceAnalytificationSchemeComparison

/-! # Analytification of separated schemes in the localized analytic category -/

noncomputable section

universe u i

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Set
open SaturatedAtlasPresentation
open AffineAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (f' : Y ⟶ Spec (CommRingCat.of K)) (f'' : Z ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] [LocallyOfFiniteType f'']

namespace Localized

private theorem openGluing : OpenGluing K f :=
  ⟨OpenGluing.isOpenEmbedding_ι K f, OpenGluing.range_ι_inter K f⟩

/-- The actual atlas glued along the affine opens of the scheme. -/
abbrev model : SaturatedAtlasPresentation.{u, u, u} K :=
  schemePresentation (openGluing K f)

/-- The localized analytic space of the glued atlas. -/
abbrev object : LocalizedCategory.{u, u, u} (K := K) := localizationFunctor.obj (model K f)

/-- The analytic domain cut out by an affine open of the scheme. -/
abbrev chartDomain (U : X.affineOpens) : (model K f).AnalyticDomain :=
  affineDomain (openGluing K f) U

/-- The existing comparison of the affine analytification with its domain. -/
abbrev chartIso (U : X.affineOpens) : localized K (chartPresentation K f U) ≅
    localizationFunctor.obj ((model K f).domain (chartDomain K f U)) :=
  affineIso (openGluing K f) U

/-- The affine chart as a morphism into the glued localized analytic space. -/
def chartInclusion (U : X.affineOpens) : localized K (chartPresentation K f U) ⟶ object K f :=
  (chartIso K f U).hom ≫ (model K f).localizedDomainInclusion (chartDomain K f U)

@[simp]
theorem chartInclusion_apply (U : X.affineOpens) (y : LocalSpace K f U) :
    localizedSpaceFunctor.map (chartInclusion K f U) y = ι K f U y := by
  change localizedSpaceFunctor.map (localizationFunctor.map (toDomain (openGluing K f) U) ≫
    localizationFunctor.map ((model K f).domainInclusion (chartDomain K f U))) y = _
  rw [← Functor.map_comp, localizedSpaceFunctor_map]
  rfl

theorem chartDomain_carrier (U : X.affineOpens) :
    (chartDomain K f U).carrier = center K f ⁻¹' ((U : X.Opens) : Set X) :=
  (OpenGluing.range_ι K f U).symm

theorem chartDomain_mono {U V : X.affineOpens} (h : (U : X.Opens) ≤ V) :
    chartDomain K f U ≤ chartDomain K f V := by
  change (chartDomain K f U).carrier ⊆ (chartDomain K f V).carrier
  rw [chartDomain_carrier, chartDomain_carrier]
  exact Set.preimage_mono h

theorem chartDomain_inter [IsSeparated f] (U V : X.affineOpens) :
    chartDomain K f (SpaceAnalytification.chartIntersection K f U V) =
      chartDomain K f U ⊓ chartDomain K f V := by
  apply SetLike.coe_injective
  change (chartDomain K f _).carrier = (chartDomain K f U).carrier ∩ (chartDomain K f V).carrier
  rw [chartDomain_carrier, chartDomain_carrier, chartDomain_carrier]
  rfl

/-- The actual restriction between two affine analytifications. -/
abbrev affineRestriction {U V : X.affineOpens} (h : (U : X.Opens) ≤ V) :
    localized K (chartPresentation K f U) ⟶ localized K (chartPresentation K f V) :=
  localizedHom K (chartPresentation K f V) (chartPresentation K f U) (restriction f h)

@[reassoc]
theorem affineRestriction_chartInclusion {U V : X.affineOpens} (h : (U : X.Opens) ≤ V) :
    affineRestriction K f h ≫ chartInclusion K f V = chartInclusion K f U := by
  change localizationFunctor.map _ ≫ localizationFunctor.map _ ≫ localizationFunctor.map _ =
    localizationFunctor.map _ ≫ localizationFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    saturatedHom_comp_toDomain _ h]

theorem affineRestriction_chartIso {U V : X.affineOpens} (h : (U : X.Opens) ≤ V) :
    affineRestriction K f h ≫ (chartIso K f V).hom =
      (chartIso K f U).hom ≫ localizedDomainMap (chartDomain_mono K f h) := by
  apply (cancel_mono ((model K f).localizedDomainInclusion (chartDomain K f V))).1
  rw [Category.assoc, Category.assoc, localizedDomainMap_inclusion]
  exact affineRestriction_chartInclusion K f h

variable (g : X ⟶ Y) (hg : g ≫ f' = f)

/-- An affine source chart and an affine target chart containing its image. -/
structure AffinePair where
  source : X.affineOpens
  target : Y.affineOpens
  le_preimage : (source : X.Opens) ≤ g ⁻¹ᵁ (target : Y.Opens)

/-- The analytic morphism of affine charts induced by the algebraic restriction. -/
abbrev affineMap {U : X.affineOpens} {V : Y.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) :
    localized K (chartPresentation K f U) ⟶ localized K (chartPresentation K f' V) :=
  localizedHom K (chartPresentation K f' V) (chartPresentation K f U) (openCoordinateMap g hg h)

private theorem affineMap_restriction {U₀ U : X.affineOpens} {V₀ V : Y.affineOpens}
    (hU : (U₀ : X.Opens) ≤ U) (hV : (V₀ : Y.Opens) ≤ V)
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (h₀ : (U₀ : X.Opens) ≤ g ⁻¹ᵁ (V₀ : Y.Opens)) :
    affineRestriction K f hU ≫ affineMap K f f' g hg h =
      affineMap K f f' g hg h₀ ≫ affineRestriction K f' hV := by
  have comp := affineAnalytificationLocalizedFunctoriality.{u,u,u,u}
  have h₁ := (comp K _ _ _ (chartPresentation K f' V) (chartPresentation K f' V)
    (chartPresentation K f U) (chartPresentation K f U₀)
    (openCoordinateMap g hg h) (restriction f hU)).2.2.2.1
  have h₂ := (comp K _ _ _ (chartPresentation K f' V) (chartPresentation K f' V)
    (chartPresentation K f' V₀) (chartPresentation K f U₀)
    (restriction f' hV) (openCoordinateMap g hg h₀)).2.2.2.1
  refine h₁.symm.trans (?_ : _ = _)
  refine (congrArg (localizedHom K (chartPresentation K f' V) (chartPresentation K f U₀))
    ?_).trans h₂
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply,
    MorphismExistence.restriction_openCoordinateMap, MorphismExistence.openCoordinateMap_restriction]

private def localArrow (p : AffinePair g) :
    localizationFunctor.obj ((model K f).domain (chartDomain K f p.source)) ⟶ object K f' :=
  (chartIso K f p.source).inv ≫ affineMap K f f' g hg p.le_preimage ≫ chartInclusion K f' p.target

private theorem localArrow_restriction (p : AffinePair g)
    {U₀ : X.affineOpens} {V₀ : Y.affineOpens}
    (hU : (U₀ : X.Opens) ≤ p.source) (hV : (V₀ : Y.Opens) ≤ p.target)
    (h₀ : (U₀ : X.Opens) ≤ g ⁻¹ᵁ (V₀ : Y.Opens)) :
    (chartIso K f U₀).hom ≫ localizedDomainMap (chartDomain_mono K f hU) ≫
      localArrow K f f' g hg p =
    affineMap K f f' g hg h₀ ≫ chartInclusion K f' V₀ := by
  rw [← Category.assoc, ← affineRestriction_chartIso K f hU, localArrow]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, affineMap_restriction K f f' g hg hU hV p.le_preimage h₀,
    Category.assoc, affineRestriction_chartInclusion]

private theorem localArrow_overlap [IsSeparated f] [IsSeparated f'] (p q : AffinePair g)
    {D : (model K f).AnalyticDomain} (hp : D ≤ chartDomain K f p.source)
    (hq : D ≤ chartDomain K f q.source)
    (hD : chartDomain K f (SpaceAnalytification.chartIntersection K f p.source q.source) = D) :
    localizedDomainMap hp ≫ localArrow K f f' g hg p =
      localizedDomainMap hq ≫ localArrow K f f' g hg q := by
  subst D
  let U₀ := SpaceAnalytification.chartIntersection K f p.source q.source
  let V₀ := SpaceAnalytification.chartIntersection K f' p.target q.target
  have h₀ : (U₀ : X.Opens) ≤ g ⁻¹ᵁ (V₀ : Y.Opens) :=
    fun _ hx => ⟨p.le_preimage hx.1, q.le_preimage hx.2⟩
  apply (cancel_epi (chartIso K f U₀).hom).1
  exact (localArrow_restriction K f f' g hg p inf_le_left inf_le_left h₀).trans
    (localArrow_restriction K f f' g hg q inf_le_right inf_le_right h₀).symm

private def matchingFamily [IsSeparated f] [IsSeparated f'] :
    LocalizedDomainMatchingFamily (model K f) (model K f')
      (fun p : AffinePair g => chartDomain K f p.source) where
  localMap := localArrow K f f' g hg
  overlap p q := localArrow_overlap K f f' g hg p q inf_le_left inf_le_right
    (chartDomain_inter K f p.source q.source)

private theorem chartDomains_cover {I : Type i} (U : I → X.affineOpens)
    (hU : ∀ x : X, ∃ j, x ∈ (U j : X.Opens)) :
    AtlasTopology.LocallyRefines (Set.range fun j => (chartDomain K f (U j)).carrier) {Set.univ} := by
  intro W hW y _
  obtain rfl := Set.mem_singleton_iff.mp hW
  obtain ⟨j, hj⟩ := hU (center K f y)
  let V := (chartDomain K f (U j)).carrier
  have hy : y ∈ V := by
    change y ∈ (chartDomain K f (U j)).carrier
    rw [chartDomain_carrier]
    exact hj
  refine ⟨{V}, Set.finite_singleton _, Set.singleton_subset_iff.mpr ⟨j, rfl⟩,
    ?_, ?_⟩
  · intro T hT
    obtain rfl := Set.mem_singleton_iff.mp hT
    exact ⟨Set.subset_univ _, hy⟩
  · rw [Set.sUnion_singleton, nhdsWithin_univ]
    apply IsOpen.mem_nhds ?_ hy
    exact (OpenGluing.isOpenEmbedding_ι K f (U j)).isOpen_range

private theorem exists_affinePair (x : X) : ∃ p : AffinePair g, x ∈ (p.source : X.Opens) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := g ⁻¹ᵁ V) hxV
  exact ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hUV⟩, hxU⟩

/-- Analytify an algebraic map of separated schemes by gluing the actual
analytic maps on all affine source opens subordinate to affine target opens. -/
def map [IsSeparated f] [IsSeparated f'] : object K f ⟶ object K f' :=
  (matchingFamily K f f' g hg).glue
    (chartDomains_cover K f AffinePair.source (exists_affinePair g))

@[reassoc]
theorem chartInclusion_map [IsSeparated f] [IsSeparated f'] {U : X.affineOpens} {V : Y.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) :
    chartInclusion K f U ≫ map K f f' g hg =
      affineMap K f f' g hg h ≫ chartInclusion K f' V := by
  rw [chartInclusion, Category.assoc]
  let p : AffinePair g := ⟨U, V, h⟩
  have hp := (matchingFamily K f f' g hg).glue_restrict
    (chartDomains_cover K f AffinePair.source (exists_affinePair g)) p
  change (model K f).localizedDomainInclusion (chartDomain K f U) ≫ map K f f' g hg =
    localArrow K f f' g hg p at hp
  rw [hp]
  simp [localArrow, p]

/-- Forgetting the analytic structure gives the existing map on glued point spaces. -/
theorem underlying_map [IsSeparated f] [IsSeparated f'] :
    (localizedSpaceFunctor.map (map K f f' g hg)).hom =
      MorphismExistence.analytification K f f' g hg := by
  apply (MorphismExistence.existsUnique_isAnalytificationMap K f f' g hg).unique
  · intro U V h y
    have he := congrArg
      (fun m : localized K (chartPresentation K f U) ⟶ object K f' =>
        localizedSpaceFunctor.map m y) (chartInclusion_map K f f' g hg h)
    rw [Functor.map_comp, Functor.map_comp] at he
    change localizedSpaceFunctor.map (map K f f' g hg)
        (localizedSpaceFunctor.map (chartInclusion K f U) y) =
      localizedSpaceFunctor.map (chartInclusion K f' V)
        (localizedSpaceFunctor.map (affineMap K f f' g hg h) y) at he
    rw [affineMap, localizedSpaceFunctor_map_localizedHom, chartInclusion_apply] at he
    exact he.trans (chartInclusion_apply K f' V (morphismLocalMap K f f' g hg h y))
  · exact MorphismExistence.isAnalytificationMap_analytification K f f' g hg

private theorem map_id [IsSeparated f] :
    map K f f (𝟙 X) (Category.id_comp _) = 𝟙 (object K f) := by
  have hcover (x : X) : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨⟨U, hU⟩, hx⟩
  apply localizedHom_ext_of_domainCover (fun U => chartDomain K f U)
    (chartDomains_cover K f id hcover)
  intro U
  apply (cancel_epi (chartIso K f U).hom).1
  suffices chartInclusion K f U ≫ map K f f (𝟙 X) (Category.id_comp _) =
      chartInclusion K f U by
    simpa only [chartInclusion, Category.assoc, Category.comp_id] using this
  rw [chartInclusion_map K f f (𝟙 X) (Category.id_comp _) (le_refl (U : X.Opens))]
  have hcoord : restriction f (le_refl (U : X.Opens)) = AlgHom.id K _ :=
    AlgHom.ext (MorphismExistence.restriction_self U)
  change localizedHom K (chartPresentation K f U) (chartPresentation K f U)
    (openCoordinateMap (𝟙 X) (Category.id_comp f) (le_refl (U : X.Opens))) ≫ _ = _
  rw [openCoordinateMap_id, hcoord]
  let P := chartPresentation K f U
  have hid := (affineAnalytificationLocalizedFunctoriality.{u,u,u,u} K _ _ _ P P P P
    (AlgHom.id K _) (AlgHom.id K _)).2.2.1
  rw [hid, Category.id_comp]

/-- Affine charts compatible with each step of a composable pair of scheme maps. -/
private structure AffineChain (k : Y ⟶ Z) where
  first : AffinePair g
  last : Z.affineOpens
  le_preimage : (first.target : Y.Opens) ≤ k ⁻¹ᵁ (last : Z.Opens)

private theorem exists_affineChain (k : Y ⟶ Z) (x : X) :
    ∃ p : AffineChain g k, x ∈ (p.first.source : X.Opens) := by
  obtain ⟨p, hp⟩ := exists_affinePair k (g x)
  obtain ⟨U, hU, hx, hUp⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := g ⁻¹ᵁ (p.source : Y.Opens)) hp
  exact ⟨⟨⟨⟨U, hU⟩, p.source, hUp⟩, p.target, p.le_preimage⟩, hx⟩

private theorem map_comp [IsSeparated f] [IsSeparated f'] [IsSeparated f'']
    (k : Y ⟶ Z) (hk : k ≫ f'' = f') :
    map K f f'' (g ≫ k) (by rw [Category.assoc, hk, hg]) =
      map K f f' g hg ≫ map K f' f'' k hk := by
  apply localizedHom_ext_of_domainCover (fun p : AffineChain g k => chartDomain K f p.first.source)
    (chartDomains_cover K f (fun p : AffineChain g k => p.first.source) (exists_affineChain g k))
  intro p
  apply (cancel_epi (chartIso K f p.first.source).hom).1
  have hp : (p.first.source : X.Opens) ≤ (g ≫ k) ⁻¹ᵁ (p.last : Z.Opens) :=
    fun _ hx => p.le_preimage (p.first.le_preimage hx)
  suffices chartInclusion K f p.first.source ≫
      map K f f'' (g ≫ k) (by rw [Category.assoc, hk, hg]) =
      chartInclusion K f p.first.source ≫ map K f f' g hg ≫ map K f' f'' k hk by
    simpa only [chartInclusion, Category.assoc] using this
  rw [chartInclusion_map K f f'' _ _ hp,
    chartInclusion_map_assoc K f f' g hg p.first.le_preimage,
    chartInclusion_map K f' f'' k hk p.le_preimage]
  have hmap : affineMap K f f'' (g ≫ k) (by rw [Category.assoc, hk, hg]) hp =
      affineMap K f f' g hg p.first.le_preimage ≫ affineMap K f' f'' k hk p.le_preimage := by
    change localizedHom K _ _ (openCoordinateMap (g ≫ k) _ hp) = _
    rw [openCoordinateMap_comp g hg k hk p.first.le_preimage p.le_preimage hp]
    exact (affineAnalytificationLocalizedFunctoriality.{u,u,u,u} K _ _ _
      (chartPresentation K f'' p.last) (chartPresentation K f'' p.last)
      (chartPresentation K f' p.first.target) (chartPresentation K f p.first.source)
      (openCoordinateMap k hk p.le_preimage) (openCoordinateMap g hg p.first.le_preimage)).2.2.2.1
  exact (congrArg (fun a => a ≫ chartInclusion K f'' p.last) hmap).trans
    (Category.assoc _ _ _)

end Localized

/-- The full subcategory of separated schemes locally of finite type over `Spec K`. -/
def separatedLocallyFiniteTypeOver : ObjectProperty (Over (Spec (CommRingCat.of K))) :=
  fun X => LocallyOfFiniteType X.hom ∧ IsSeparated X.hom

/-- The analytification functor with values in the localized analytic category. -/
def localizedAnalytification :
    (separatedLocallyFiniteTypeOver K).FullSubcategory ⥤ LocalizedCategory.{u, u, u} (K := K) where
  obj X :=
    letI : LocallyOfFiniteType X.obj.hom := X.property.1
    Localized.object K X.obj.hom
  map {X Y} g :=
    letI : LocallyOfFiniteType X.obj.hom := X.property.1
    letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
    letI : IsSeparated X.obj.hom := X.property.2
    letI : IsSeparated Y.obj.hom := Y.property.2
    Localized.map K X.obj.hom Y.obj.hom g.hom.left (Over.w g.hom)
  map_id X := by
    let : LocallyOfFiniteType X.obj.hom := X.property.1
    let : IsSeparated X.obj.hom := X.property.2
    exact Localized.map_id K X.obj.hom
  map_comp {X Y Z} g k := by
    let : LocallyOfFiniteType X.obj.hom := X.property.1
    let : LocallyOfFiniteType Y.obj.hom := Y.property.1
    let : LocallyOfFiniteType Z.obj.hom := Z.property.1
    let : IsSeparated X.obj.hom := X.property.2
    let : IsSeparated Y.obj.hom := Y.property.2
    let : IsSeparated Z.obj.hom := Z.property.2
    exact Localized.map_comp K X.obj.hom Y.obj.hom Z.obj.hom g.hom.left
      (Over.w g.hom) k.hom.left (Over.w k.hom)

/-- Underlying spaces and maps agree naturally with the topological analytification. -/
def localizedAnalytificationTopologicalIso :
    localizedAnalytification K ⋙ localizedSpaceFunctor ≅
      (locallyFiniteTypeOver K).lift (separatedLocallyFiniteTypeOver K).ι
        (fun X => X.property.1) ⋙ topologicalAnalytification K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y g
    let : LocallyOfFiniteType X.obj.hom := X.property.1
    let : LocallyOfFiniteType Y.obj.hom := Y.property.1
    let : IsSeparated X.obj.hom := X.property.2
    let : IsSeparated Y.obj.hom := Y.property.2
    simp only [Iso.refl_hom]
    apply TopCat.hom_ext
    exact Localized.underlying_map K X.obj.hom Y.obj.hom g.hom.left (Over.w g.hom))

end Langlands.Analytic.SchemeAnalytification
