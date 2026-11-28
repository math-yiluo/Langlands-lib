import Langlands.Geometry.Analytic.LocalizedOpenRelationSpace
import Langlands.Geometry.Analytic.LocalizedAffinoidChartFactorization
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartNeighborhoods
import Langlands.Geometry.Analytic.OriginalDomainLocalization

/-! # The affinoid atlas of the glued space

The charts of the glued space are the images of the charts of the pieces. A chart is
presented by a chosen chart of a piece with that image, and the bounded restriction between
two charts is read off from the transfer of morphisms between the pieces. -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation

open _root_.CategoryTheory Set Topology IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (R : LocalizedOpenRelation K)

/-- The atlas of the presentation of a piece. -/
abbrev atl (m : R.M) :
    IndexedAffinoidAtlas.{u, u, u} K (presentationOf (R.Z m)).presentation.space :=
  (presentationOf (R.Z m)).presentation.atlas

/-- A chart of one of the pieces. -/
structure PieceChart where
  /-- The piece. -/
  m : R.M
  /-- The chart of the piece. -/
  i : (R.atl m).Index

variable {R}

namespace PieceChart

/-- The algebra of a chart of a piece. -/
abbrev alg (c : R.PieceChart) : PresentedAffinoidAlgebra K := (R.atl c.m).algebra c.i

/-- The chart map of a chart of a piece, into the points of the piece. -/
def chart (c : R.PieceChart) : BanachSpectrum c.alg → localizedSpaceFunctor.obj (R.Z c.m) :=
  (R.atl c.m).chart c.i

/-- The domain of a chart of a piece. -/
def dom (c : R.PieceChart) : Set (localizedSpaceFunctor.obj (R.Z c.m)) := range c.chart

/-- The image of a chart of a piece in the glued space. -/
def image (c : R.PieceChart) : Set R.Space := R.ι c.m '' c.dom

end PieceChart

/-! ## Morphisms from affinoid spectra into charts of the pieces -/

/-- The small spectrum of a presented affinoid algebra, as an analytic space. -/
abbrev spec (S : PresentedAffinoidAlgebra K) : LocalizedCategory.{u, u, u} (K := K) :=
  localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, u} S)

/-- The global chart of the small spectrum. -/
abbrev gchart (S : PresentedAffinoidAlgebra K) :
    BanachSpectrum ((SmallAffinoidSpectrum.saturated.{u, u} S).presentation.atlas.algebra
      (SmallAffinoidSpectrum.globalIndex.{u, u} S)) → localizedSpaceFunctor.obj (spec S) :=
  (SmallAffinoidSpectrum.saturated.{u, u} S).presentation.atlas.chart
    (SmallAffinoidSpectrum.globalIndex.{u, u} S)

theorem exists_gchart (S : PresentedAffinoidAlgebra K) (y : localizedSpaceFunctor.obj (spec S)) :
    ∃ s, gchart S s = y := by
  have h : range (gchart S) = univ := SmallAffinoidSpectrum.globalRange.{u, u} S
  have hy : y ∈ range (gchart S) := by rw [h]; exact mem_univ y
  exact hy

theorem lsf_map_apply {A B : SaturatedAtlasPresentation.{u, u, u} K} (f : A ⟶ B)
    (y : A.presentation.space) :
    localizedSpaceFunctor.map (localizationFunctor.map f) y = f.baseMap y := by
  rw [localizedSpaceFunctor_map]; rfl

/-- The map on spectra of a bounded map, as a localized morphism. -/
abbrev smap {S S' : PresentedAffinoidAlgebra K} (θ : BoundedAlgHom K S S') :
    spec S' ⟶ spec S :=
  localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} θ)

variable (R) in
/-- The localized morphism from the spectrum of `S` into a piece given by a bounded map out of
the algebra of one of its charts. -/
def cmap (S : PresentedAffinoidAlgebra K) (c : R.PieceChart) (φ : BoundedAlgHom K c.alg S) :
    spec S ⟶ R.Z c.m :=
  localizationFunctor.map (SmallAffinoidSpectrum.chartMap.{u, u} S (B := presentationOf (R.Z c.m))
    c.i φ)

/-- The inclusion of the spectrum of a chart of a piece. -/
abbrev incl (c : R.PieceChart) : spec c.alg ⟶ R.Z c.m :=
  R.cmap c.alg c (BoundedAlgHom.id K c.alg)

omit [CompleteSpace K] in
theorem comap_cast {A S S' : PresentedAffinoidAlgebra K} (h : S = S')
    (φ : BoundedAlgHom K A S) (x : BanachSpectrum S) :
    BanachSpectrum.comap (h ▸ φ : BoundedAlgHom K A S').toBoundedRingHom (h ▸ x) =
      BanachSpectrum.comap φ.toBoundedRingHom x := by
  subst h; rfl

theorem cmap_gchart (S : PresentedAffinoidAlgebra K) (c : R.PieceChart)
    (φ : BoundedAlgHom K c.alg S) (s) :
    localizedSpaceFunctor.map (R.cmap S c φ) (gchart S s) =
      c.chart (BanachSpectrum.comap
        ((SmallAffinoidSpectrum.globalAlgebra.{u, u} S).symm ▸ φ :
          BoundedAlgHom K c.alg _).toBoundedRingHom s) := by
  rw [show localizedSpaceFunctor.map (R.cmap S c φ) (gchart S s) =
    (SmallAffinoidSpectrum.chartMap.{u, u} S (B := presentationOf (R.Z c.m)) c.i φ).baseMap
      (gchart S s) from lsf_map_apply _ _]
  exact chartSourceMap_chart _ _ _ _ s

/-- The point formula for the morphism of a bounded map, at a point of the algebra. -/
theorem cmap_apply (S : PresentedAffinoidAlgebra K) (c : R.PieceChart)
    (φ : BoundedAlgHom K c.alg S) (x : BanachSpectrum S) :
    localizedSpaceFunctor.map (R.cmap S c φ)
        (gchart S ((SmallAffinoidSpectrum.globalAlgebra.{u, u} S).symm ▸ x)) =
      c.chart (BanachSpectrum.comap φ.toBoundedRingHom x) := by
  rw [cmap_gchart, comap_cast]

theorem cmap_mem (S : PresentedAffinoidAlgebra K) (c : R.PieceChart)
    (φ : BoundedAlgHom K c.alg S) (y : localizedSpaceFunctor.obj (spec S)) :
    localizedSpaceFunctor.map (R.cmap S c φ) y ∈ c.dom := by
  rw [show localizedSpaceFunctor.map (R.cmap S c φ) y =
    (SmallAffinoidSpectrum.chartMap.{u, u} S (B := presentationOf (R.Z c.m)) c.i φ).baseMap y
      from lsf_map_apply _ _]
  exact SmallAffinoidSpectrum.chartMap_mem S c.i φ y

theorem cmap_injective (S : PresentedAffinoidAlgebra K) (c : R.PieceChart) :
    Function.Injective (R.cmap S c) :=
  SmallAffinoidSpectrum.localizedChartMap_injective (B := presentationOf (R.Z c.m)) S c.i

theorem exists_cmap_eq (S : PresentedAffinoidAlgebra K) (c : R.PieceChart)
    (f : spec S ⟶ R.Z c.m) (hf : ∀ y, localizedSpaceFunctor.map f y ∈ c.dom) :
    ∃ φ, R.cmap S c φ = f := by
  obtain ⟨φ, hφ, -⟩ := SmallAffinoidSpectrum.localizedAffinoidChartFactorization
    (presentationOf (R.Z c.m)) S c.i f hf
  exact ⟨φ, hφ⟩

theorem smap_cmap {S S' : PresentedAffinoidAlgebra K} (θ : BoundedAlgHom K S S')
    (c : R.PieceChart) (φ : BoundedAlgHom K c.alg S) :
    smap θ ≫ R.cmap S c φ = R.cmap S' c (θ.comp φ) := by
  have h := SmallAffinoidSpectrum.map_comp_chartMap.{u, u} θ (B := presentationOf (R.Z c.m)) c.i φ
  exact (localizationFunctor.map_comp _ _).symm.trans (congrArg localizationFunctor.map h)

theorem smap_incl (c : R.PieceChart) {S : PresentedAffinoidAlgebra K}
    (θ : BoundedAlgHom K c.alg S) : smap θ ≫ incl c = R.cmap S c θ := by
  rw [smap_cmap, BoundedAlgHom.comp_id]

/-! ## Factorization through charts of the pieces -/

/-- A morphism from an affinoid spectrum into a piece whose image lies in the image of a chart
`c` of a piece is related to the morphism of a unique bounded map out of the algebra of `c`. -/
theorem existsUnique_pbc (S : PresentedAffinoidAlgebra K) {m : R.M} (f : spec S ⟶ R.Z m)
    (c : R.PieceChart) (hf : ∀ y, R.ι m (localizedSpaceFunctor.map f y) ∈ c.image) :
    ∃! φ : BoundedAlgHom K c.alg S, R.Rel f (R.cmap S c φ) := by
  have hd : ∀ y, localizedSpaceFunctor.map f y ∈ R.domainSet m c.m := by
    intro y
    rw [← preimage_range_ι]
    obtain ⟨z, -, hz⟩ := hf y
    exact ⟨z, hz⟩
  let g := transfer c.m f hd
  have hg : ∀ y, localizedSpaceFunctor.map g y ∈ c.dom := by
    intro y
    have hy := hf y
    rw [(rel_transfer c.m f hd).ι_apply] at hy
    obtain ⟨z, hz, h⟩ := hy
    rwa [← injective_ι _ h]
  obtain ⟨φ, hφ⟩ := exists_cmap_eq S c g hg
  refine ⟨φ, show R.Rel f (R.cmap S c φ) by rw [hφ]; exact rel_transfer c.m f hd,
    fun ψ hψ => cmap_injective S c ?_⟩
  rw [hφ]
  exact hψ.eq_transfer

/-- The bounded map out of the algebra of a chart of a piece. -/
def pbc (S : PresentedAffinoidAlgebra K) {m : R.M} (f : spec S ⟶ R.Z m) (c : R.PieceChart)
    (hf : ∀ y, R.ι m (localizedSpaceFunctor.map f y) ∈ c.image) : BoundedAlgHom K c.alg S :=
  Classical.choose (existsUnique_pbc S f c hf).exists

theorem rel_pbc (S : PresentedAffinoidAlgebra K) {m : R.M} (f : spec S ⟶ R.Z m)
    (c : R.PieceChart) (hf : ∀ y, R.ι m (localizedSpaceFunctor.map f y) ∈ c.image) :
    R.Rel f (R.cmap S c (pbc S f c hf)) :=
  Classical.choose_spec (existsUnique_pbc S f c hf).exists

theorem pbc_unique (S : PresentedAffinoidAlgebra K) {m : R.M} (f : spec S ⟶ R.Z m)
    (c : R.PieceChart) (hf : ∀ y, R.ι m (localizedSpaceFunctor.map f y) ∈ c.image)
    (ψ : BoundedAlgHom K c.alg S) (hψ : R.Rel f (R.cmap S c ψ)) :
    ψ = pbc S f c hf :=
  (existsUnique_pbc S f c hf).unique hψ (rel_pbc S f c hf)

theorem incl_mem_image (c : R.PieceChart) (y : localizedSpaceFunctor.obj (spec c.alg)) :
    R.ι c.m (localizedSpaceFunctor.map (incl c) y) ∈ c.image :=
  ⟨_, cmap_mem _ _ _ y, rfl⟩

/-- The bounded map from the algebra of a chart `d` of a piece to the algebra of a chart `c` of
a piece whose image lies in the image of `d`. -/
def rho (c d : R.PieceChart) (h : c.image ⊆ d.image) : BoundedAlgHom K d.alg c.alg :=
  pbc c.alg (incl c) d fun y => h (incl_mem_image c y)

theorem rel_rho (c d : R.PieceChart) (h : c.image ⊆ d.image) :
    R.Rel (incl c) (R.cmap c.alg d (rho c d h)) :=
  rel_pbc _ _ _ _

theorem rho_unique (c d : R.PieceChart) (h : c.image ⊆ d.image) (ψ : BoundedAlgHom K d.alg c.alg)
    (hψ : R.Rel (incl c) (R.cmap c.alg d ψ)) : ψ = rho c d h :=
  pbc_unique _ _ _ _ ψ hψ

theorem cmap_rho (c d : R.PieceChart) (h : c.image ⊆ d.image) (S : PresentedAffinoidAlgebra K)
    (ψ : BoundedAlgHom K c.alg S) :
    R.Rel (R.cmap S c ψ) (R.cmap S d (ψ.comp (rho c d h))) := by
  rw [← smap_incl, ← smap_cmap]
  exact (rel_rho c d h).comp _

theorem rho_self (c : R.PieceChart) (h : c.image ⊆ c.image) :
    rho c c h = BoundedAlgHom.id K c.alg :=
  (rho_unique c c h _ (Rel.refl _)).symm

theorem rho_comp (c d e : R.PieceChart) (hcd : c.image ⊆ d.image) (hde : d.image ⊆ e.image)
    (hce : c.image ⊆ e.image) :
    rho c e hce = (rho c d hcd).comp (rho d e hde) :=
  (rho_unique c e hce _ ((rel_rho c d hcd).trans (cmap_rho d e hde c.alg _))).symm

omit [CompleteSpace K] in
theorem cast_symm_cast {S S' : PresentedAffinoidAlgebra K} (h : S' = S) (s : BanachSpectrum S') :
    (h.symm ▸ (h ▸ s : BanachSpectrum S) : BanachSpectrum S') = s := by
  subst h; rfl

theorem exists_gchart_cast (S : PresentedAffinoidAlgebra K)
    (y : localizedSpaceFunctor.obj (spec S)) :
    ∃ x : BanachSpectrum S, gchart S ((SmallAffinoidSpectrum.globalAlgebra.{u, u} S).symm ▸ x) = y := by
  obtain ⟨s, rfl⟩ := exists_gchart S y
  exact ⟨(SmallAffinoidSpectrum.globalAlgebra.{u, u} S) ▸ s, by rw [cast_symm_cast]⟩

theorem rho_chart (c d : R.PieceChart) (h : c.image ⊆ d.image) (x : BanachSpectrum c.alg) :
    R.ι d.m (d.chart (BanachSpectrum.comap (rho c d h).toBoundedRingHom x)) =
      R.ι c.m (c.chart x) := by
  have e := (rel_rho c d h).ι_apply
    (gchart c.alg ((SmallAffinoidSpectrum.globalAlgebra.{u, u} c.alg).symm ▸ x))
  rw [cmap_apply, cmap_apply] at e
  exact e.symm

theorem rho_universal (c d : R.PieceChart) (h : c.image ⊆ d.image)
    (S : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K d.alg S)
    (hφ : ∀ x, R.ι d.m (d.chart (BanachSpectrum.comap φ.toBoundedRingHom x)) ∈ c.image) :
    ∃! ψ : BoundedAlgHom K c.alg S, ψ.comp (rho c d h) = φ := by
  let g := R.cmap S d φ
  have hg : ∀ y, R.ι d.m (localizedSpaceFunctor.map g y) ∈ c.image := by
    intro y
    obtain ⟨x, rfl⟩ := exists_gchart_cast S y
    rw [cmap_apply]
    exact hφ x
  refine ⟨pbc S g c hg, ?_, fun ψ hψ => ?_⟩
  · apply cmap_injective S d
    exact (cmap_rho c d h S (pbc S g c hg)).unique (rel_pbc S g c hg).symm
  · apply pbc_unique S g c hg
    have h1 := cmap_rho c d h S ψ
    rw [hψ] at h1
    exact h1.symm

/-! ## Chart images -/

variable (R) in
/-- The images in the glued space of the charts of the pieces. -/
def ChartImage : Type u := {T : Set R.Space // ∃ c : R.PieceChart, c.image = T}

namespace ChartImage

/-- A chosen chart of a piece with the given image. -/
def rep (T : R.ChartImage) : R.PieceChart := Classical.choose T.2

theorem rep_image (T : R.ChartImage) : T.rep.image = T.1 := Classical.choose_spec T.2

end ChartImage

/-- The chart map of a chart image. -/
def chartMap (T : R.ChartImage) : BanachSpectrum T.rep.alg → R.Space :=
  fun x => R.ι T.rep.m (T.rep.chart x)

theorem range_chartMap (T : R.ChartImage) : range (chartMap T) = T.1 := by
  rw [← T.rep_image, PieceChart.image, PieceChart.dom, ← range_comp]
  rfl

/-- The preimage in a piece of the image of a chart of a piece is an analytic domain. -/
theorem isOriginalChartDomain_preimage_image (m : R.M) (c : R.PieceChart) :
    (R.atl m).IsOriginalChartDomain
      {z : (presentationOf (R.Z m)).presentation.space | R.ι m z ∈ c.image} := by
  let W := R.domainSet m c.m
  have hW : IsOpen W := R.isOpen_domainSet m c.m
  let D := (presentationOf (R.Z m)).openDomain W hW
  let ν := domainι (R.Z m) D
  have hν : ∀ x, localizedSpaceFunctor.map ν x ∈ R.domainSet m c.m := fun x => by
    rw [domainι_apply]; exact x.property
  let τ := transfer c.m ν hν
  let F := domainPreimage τ ((presentationOf (R.Z c.m)).chartDomain c.i)
  have hE : {z : (presentationOf (R.Z m)).presentation.space | R.ι m z ∈ c.image} =
      (D.subspaceExtend F : Set _) := by
    ext z
    constructor
    · rintro ⟨z', hz', hzz⟩
      have hz : z ∈ W := by
        show z ∈ R.domainSet m c.m
        rw [← preimage_range_ι]; exact ⟨z', hzz⟩
      let w : localizedSpaceFunctor.obj (domainObj (R.Z m) D) := ⟨z, hz⟩
      have hw : localizedSpaceFunctor.map ν w = z := domainι_apply _ w
      refine ⟨w, ?_, rfl⟩
      change localizedSpaceFunctor.map τ w ∈ c.dom
      have e := (rel_transfer c.m ν hν).ι_apply w
      rw [hw, ← hzz] at e
      exact (injective_ι _ e) ▸ hz'
    · rintro ⟨w, hw, rfl⟩
      have e := (rel_transfer c.m ν hν).ι_apply w
      have hw' : localizedSpaceFunctor.map ν w = w.val := domainι_apply _ w
      show R.ι m w.val ∈ c.image
      rw [← hw', e]
      exact ⟨_, hw, rfl⟩
  rw [hE]
  exact (D.subspaceExtend F).is_domain

end Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation
