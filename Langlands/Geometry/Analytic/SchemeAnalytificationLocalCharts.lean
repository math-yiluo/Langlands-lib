import Langlands.Geometry.Analytic.SchemeAnalytificationAffinoidPoints

/-! # Local affinoid charts of the glued analytification of a scheme -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification
open AffineAnalytification AffineAnalytification.LocalDomainMaps AffinoidPoints
open IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- A local chart of the glued analytification: an affine open `U` of `X` together with a
local affinoid domain of the polynomial-locus atlas of the analytification of `U`. -/
structure LocalChart where
  affineOpen : X.affineOpens
  domain : LocalDomain (atlas K (chartPresentation K f affineOpen))

namespace LocalChart

variable {K f}

/-- The affinoid algebra of a local chart. -/
abbrev algebra (G : LocalChart K f) : PresentedAffinoidAlgebra K := G.domain.algebra

/-- The map from the global sections of the affine open to the algebra of a local chart. -/
def coord (G : LocalChart K f) :
    CoordinateRing (structureMap f G.affineOpen) →ₐ[K] G.algebra :=
  localAlgebraMap (chartPresentation K f G.affineOpen) G.domain

/-- The scheme morphism `Spec B → X` of a local chart with algebra `B`. -/
def point (G : LocalChart K f) : Spec (CommRingCat.of G.algebra) ⟶ X :=
  schemePoint G.affineOpen G.coord

/-- The spectrum of the algebra of a local chart, mapped into the glued analytification. -/
def chart (G : LocalChart K f) : BanachSpectrum G.algebra → Space K f :=
  fun x => ι K f G.affineOpen (G.domain.ambientMap x)

/-- The image of a local chart in the glued analytification. -/
def image (G : LocalChart K f) : Set (Space K f) :=
  ι K f G.affineOpen '' G.domain.locus

theorem chart_apply (G : LocalChart K f) (x : BanachSpectrum G.algebra) :
    G.chart x = ι K f G.affineOpen (G.domain.ambientMap x) :=
  rfl

theorem range_chart (G : LocalChart K f) : Set.range G.chart = G.image := by
  rw [image, ← G.domain.range_ambientMap, ← Set.range_comp]
  rfl

theorem chart_mem_image (G : LocalChart K f) (x : BanachSpectrum G.algebra) :
    G.chart x ∈ G.image := by
  rw [← G.range_chart]
  exact Set.mem_range_self x

theorem continuous_chart (G : LocalChart K f) : Continuous G.chart :=
  (ι K f G.affineOpen).continuous.comp G.domain.ambientMap.continuous

theorem chart_injective (G : LocalChart K f) (hι : Function.Injective (ι K f G.affineOpen)) :
    Function.Injective G.chart :=
  hι.comp G.domain.isEmbedding_ambientMap.injective

theorem isEmbedding_chart (G : LocalChart K f) (hι : IsEmbedding (ι K f G.affineOpen)) :
    IsEmbedding G.chart :=
  hι.comp G.domain.isEmbedding_ambientMap

/-- Bounded maps out of the algebra of a local chart are determined by their scheme
morphisms. -/
theorem hom_ext (G : LocalChart K f) {R : PresentedAffinoidAlgebra K}
    {ψ ψ' : BoundedAlgHom K G.algebra R}
    (h : schemePoint G.affineOpen (ψ.toAlgHom.comp G.coord) =
      schemePoint G.affineOpen (ψ'.toAlgHom.comp G.coord)) : ψ = ψ' :=
  localDomain_hom_ext _ G.domain ψ ψ' fun a =>
    DFunLike.congr_fun (schemePoint_injective G.affineOpen h) a

/-- The point of the glued analytification given by a bounded map out of the algebra of a
local chart, computed from any description of its scheme morphism. -/
theorem chart_comap (G : LocalChart K f) {R : PresentedAffinoidAlgebra K}
    (ψ : BoundedAlgHom K G.algebra R) {U'' : X.affineOpens}
    (α'' : CoordinateRing (structureMap f U'') →ₐ[K] R)
    (h : schemePoint G.affineOpen (ψ.toAlgHom.comp G.coord) = schemePoint U'' α'')
    (x : BanachSpectrum R) :
    G.chart (BanachSpectrum.comap ψ.toBoundedRingHom x) =
      ι K f U'' (affinoidBaseMap K (chartPresentation K f U'') R α'' x) := by
  rw [chart_apply, ambientMap_comap]
  exact ι_affinoidBaseMap_eq K f _ α'' h x

/-- Existence half of the universal property of a local chart: an algebra map out of the
global sections of an affine open whose spectrum points land in the image of the chart
factors through the algebra of the chart, at the level of scheme morphisms. -/
theorem exists_lift (G : LocalChart K f) (hι : Function.Injective (ι K f G.affineOpen))
    {R : PresentedAffinoidAlgebra K} {U'' : X.affineOpens}
    (α'' : CoordinateRing (structureMap f U'') →ₐ[K] R)
    (h : ∀ x, ι K f U'' (affinoidBaseMap K (chartPresentation K f U'') R α'' x) ∈ G.image) :
    ∃ ψ : BoundedAlgHom K G.algebra R,
      schemePoint G.affineOpen (ψ.toAlgHom.comp G.coord) = schemePoint U'' α'' := by
  have hrange : Set.range (schemePoint U'' α'') ⊆ ((G.affineOpen : X.Opens) : Set X) := by
    apply range_schemePoint_subset K f U'' α'' G.affineOpen.1
    intro x
    obtain ⟨y, -, hy⟩ := h x
    rw [← center_ι, ← hy]
    exact center_ι_mem K f G.affineOpen y
  obtain ⟨α, hα⟩ := exists_schemePoint_eq U'' G.affineOpen α'' hrange
  have hlocus : ∀ x, affinoidBaseMap K (chartPresentation K f G.affineOpen) R α x ∈
      G.domain.locus := by
    intro x
    obtain ⟨y, hy, hyx⟩ := h x
    have e := ι_affinoidBaseMap_eq K f α α'' hα x
    rw [← hyx] at e
    rw [hι e]
    exact hy
  obtain ⟨ψ, hψ⟩ := exists_localDomain_lift (chartPresentation K f G.affineOpen) G.domain R α
    hlocus
  refine ⟨ψ, ?_⟩
  rw [coord, hψ, hα]

/-- A scheme morphism through a local chart, followed by a further bounded map. -/
theorem schemePoint_comp_coord (G : LocalChart K f) {R : PresentedAffinoidAlgebra K}
    (ψ : BoundedAlgHom K G.algebra R) :
    schemePoint G.affineOpen (ψ.toAlgHom.comp G.coord) =
      Spec.map (CommRingCat.ofHom ψ.toAlgHom.toRingHom) ≫ G.point :=
  schemePoint_comp G.affineOpen G.coord ψ.toAlgHom

/-! ## Compatible bounded maps -/

/-- A bounded map from the algebra of `G'` to the algebra of `G` is compatible if it
identifies the scheme morphism of `G` with the composite through `G'`. -/
def Compatible (G G' : LocalChart K f) (ρ : BoundedAlgHom K G'.algebra G.algebra) : Prop :=
  schemePoint G'.affineOpen (ρ.toAlgHom.comp G'.coord) = G.point

theorem Compatible.schemePoint_comp {G G' : LocalChart K f}
    {ρ : BoundedAlgHom K G'.algebra G.algebra} (hρ : Compatible G G' ρ)
    {R : PresentedAffinoidAlgebra K} (ψ : BoundedAlgHom K G.algebra R) :
    schemePoint G'.affineOpen ((ψ.comp ρ).toAlgHom.comp G'.coord) =
      schemePoint G.affineOpen (ψ.toAlgHom.comp G.coord) := by
  change schemePoint G'.affineOpen (ψ.toAlgHom.comp (ρ.toAlgHom.comp G'.coord)) = _
  rw [AffinoidPoints.schemePoint_comp, hρ, point, ← AffinoidPoints.schemePoint_comp]

theorem compatible_unique {G G' : LocalChart K f} {ρ ρ' : BoundedAlgHom K G'.algebra G.algebra}
    (h : Compatible G G' ρ) (h' : Compatible G G' ρ') : ρ = ρ' :=
  G'.hom_ext (h.trans h'.symm)

theorem compatible_id (G : LocalChart K f) :
    Compatible G G (BoundedAlgHom.id K G.algebra) :=
  rfl

theorem Compatible.comp {G₁ G₂ G₃ : LocalChart K f}
    {ρ₁ : BoundedAlgHom K G₂.algebra G₁.algebra} {ρ₂ : BoundedAlgHom K G₃.algebra G₂.algebra}
    (h₁ : Compatible G₁ G₂ ρ₁) (h₂ : Compatible G₂ G₃ ρ₂) :
    Compatible G₁ G₃ (ρ₁.comp ρ₂) :=
  (h₂.schemePoint_comp ρ₁).trans h₁

theorem Compatible.chart {G G' : LocalChart K f} {ρ : BoundedAlgHom K G'.algebra G.algebra}
    (hρ : Compatible G G' ρ) (x : BanachSpectrum G.algebra) :
    G'.chart (BanachSpectrum.comap ρ.toBoundedRingHom x) = G.chart x := by
  rw [G'.chart_comap ρ G.coord hρ x, coord, affinoidBaseMap_localAlgebraMap]
  rfl

/-- Restrictions along inclusions of local domains of the same affine open are compatible. -/
theorem compatible_inclusion {U : X.affineOpens}
    {L L' : LocalDomain (atlas K (chartPresentation K f U))} (i : L ⟶ L') :
    Compatible (⟨U, L⟩ : LocalChart K f) ⟨U, L'⟩ i.restriction := by
  change schemePoint U (i.restriction.toAlgHom.comp
    (localAlgebraMap (chartPresentation K f U) L')) =
      schemePoint U (localAlgebraMap (chartPresentation K f U) L)
  congr 1
  exact AlgHom.ext fun a => inclusion_localAlgebraMap _ i a

/-- The bounded pullbacks of the saturated morphism induced by the restriction from an affine
open `U` to a smaller affine open `V` are compatible. -/
theorem compatible_saturatedHom {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U)
    (S : (saturated K (chartPresentation K f V)).presentation.atlas.Index)
    (T : (saturated K (chartPresentation K f U)).presentation.atlas.Index)
    (h : (saturatedHom K (chartPresentation K f U) (chartPresentation K f V)
        (restriction f hVU)).baseMap ''
          Set.range ((saturated K (chartPresentation K f V)).presentation.atlas.chart S) ⊆
        Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart T)) :
    Compatible
      (⟨V, (presentation K (chartPresentation K f V)).atlas.saturatedRepresentative S⟩ :
        LocalChart K f)
      ⟨U, (presentation K (chartPresentation K f U)).atlas.saturatedRepresentative T⟩
      ((saturatedHom K (chartPresentation K f U) (chartPresentation K f V)
        (restriction f hVU)).pullback S T h) := by
  change schemePoint U (((saturatedHom K _ _ (restriction f hVU)).pullback S T h).toAlgHom.comp
    (localAlgebraMap (chartPresentation K f U)
      ((presentation K (chartPresentation K f U)).atlas.saturatedRepresentative T))) =
      schemePoint V (localAlgebraMap (chartPresentation K f V)
        ((presentation K (chartPresentation K f V)).atlas.saturatedRepresentative S))
  rw [← schemePoint_restriction hVU]
  congr 1
  exact AlgHom.ext fun a => saturatedHom_pullback_localAlgebraMap _ _ _ S T h a

/-! ## Cross-chart restrictions -/

variable (hι : ∀ U : X.affineOpens, Function.Injective (ι K f U))
include hι

theorem exists_compatible {G G' : LocalChart K f} (h : G.image ⊆ G'.image) :
    ∃ ρ : BoundedAlgHom K G'.algebra G.algebra, Compatible G G' ρ :=
  G'.exists_lift (hι _) G.coord fun x => by
    rw [coord, affinoidBaseMap_localAlgebraMap]
    exact h (G.chart_mem_image x)

omit hι in
/-- The bounded restriction from the algebra of a local chart to the algebra of a local chart
with smaller image. -/
def cross (hι : ∀ U : X.affineOpens, Function.Injective (ι K f U)) (G G' : LocalChart K f)
    (h : G.image ⊆ G'.image) : BoundedAlgHom K G'.algebra G.algebra :=
  (exists_compatible hι h).choose

theorem cross_compatible {G G' : LocalChart K f} (h : G.image ⊆ G'.image) :
    Compatible G G' (cross hι G G' h) :=
  (exists_compatible hι h).choose_spec

theorem eq_cross {G G' : LocalChart K f} (h : G.image ⊆ G'.image)
    {ρ : BoundedAlgHom K G'.algebra G.algebra} (hρ : Compatible G G' ρ) :
    ρ = cross hι G G' h :=
  compatible_unique hρ (cross_compatible hι h)

theorem cross_chart {G G' : LocalChart K f} (h : G.image ⊆ G'.image)
    (x : BanachSpectrum G.algebra) :
    G'.chart (BanachSpectrum.comap (cross hι G G' h).toBoundedRingHom x) = G.chart x :=
  (cross_compatible hι h).chart x

theorem cross_self (G : LocalChart K f) (h : G.image ⊆ G.image) :
    cross hι G G h = BoundedAlgHom.id K G.algebra :=
  (eq_cross hι h (compatible_id G)).symm

theorem cross_trans {G G' G'' : LocalChart K f} (h : G.image ⊆ G'.image)
    (h' : G'.image ⊆ G''.image) (h'' : G.image ⊆ G''.image) :
    cross hι G G'' h'' = (cross hι G G' h).comp (cross hι G' G'' h') :=
  (eq_cross hι h'' ((cross_compatible hι h).comp (cross_compatible hι h'))).symm

/-- Universal property of the cross-chart restriction. -/
theorem cross_universal {G G' : LocalChart K f} (h : G.image ⊆ G'.image)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K G'.algebra R)
    (hφ : ∀ x, G'.chart (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ G.image) :
    ∃! ψ : BoundedAlgHom K G.algebra R, ψ.comp (cross hι G G' h) = φ := by
  obtain ⟨ψ, hψ⟩ := G.exists_lift (hι _) (φ.toAlgHom.comp G'.coord) fun x => by
    rw [← G'.chart_comap φ (φ.toAlgHom.comp G'.coord) rfl x]
    exact hφ x
  refine ⟨ψ, G'.hom_ext ?_, fun ψ' hψ' => G.hom_ext ?_⟩
  · rw [(cross_compatible hι h).schemePoint_comp ψ, hψ]
  · rw [← (cross_compatible hι h).schemePoint_comp ψ', hψ', ← hψ]

theorem range_comap_cross {G G' : LocalChart K f} (h : G.image ⊆ G'.image) :
    Set.range (BanachSpectrum.comap (cross hι G G' h).toBoundedRingHom) =
      G'.chart ⁻¹' G.image := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, cross_chart]
    exact G.chart_mem_image x
  · intro hy
    rw [Set.mem_preimage, ← G.range_chart] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, G'.chart_injective (hι _) ?_⟩
    rw [cross_chart, hx]

/-- The cross-chart restriction represents the preimage of the smaller image. -/
theorem represents_cross {G G' : LocalChart K f} (h : G.image ⊆ G'.image) :
    Represents K (cross hι G G' h) (G'.chart ⁻¹' G.image) := by
  refine ⟨?_, range_comap_cross hι h, fun R φ hφ => cross_universal hι h R φ hφ⟩
  rw [← range_comap_cross hι h]
  exact (isCompact_range
    (BanachSpectrum.comapContinuous (cross hι G G' h).toBoundedRingHom).continuous).isClosed

end LocalChart

end Langlands.Analytic.SchemeAnalytification
