import Langlands.Geometry.Analytic.LocalizedOpenRelationQuotient
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts

/-! # The glued space is the quotient of the gluing data

Related morphisms into two pieces have the same composite into the glued space, and every
square formed by the relation and two pieces is a pullback. -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology IndexedAffinoidAtlas
open PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {R : LocalizedOpenRelation K}

variable (R) in
/-- The localized morphism from an affinoid spectrum into the glued space given by a bounded map
out of the algebra of a chart image. -/
abbrev ymap (S : PresentedAffinoidAlgebra K) (T : R.ChartImage)
    (ψ : BoundedAlgHom K T.rep.alg S) : spec S ⟶ R.glued :=
  localizationFunctor.map (SmallAffinoidSpectrum.chartMap.{u, u} S (B := R.presentation) T ψ)

theorem rep_image_of_subset {c : R.PieceChart} {T : R.ChartImage} (hcT : c.image ⊆ T.1) :
    c.image ⊆ T.rep.image := by
  rw [T.rep_image]; exact hcT

/-- On a chart of a piece, the morphism into the glued space is the chart map of a chart image
containing it. -/
theorem cmap_ιL (S : PresentedAffinoidAlgebra K) (c : R.PieceChart)
    (φ : BoundedAlgHom K c.alg S) (T : R.ChartImage) (hcT : c.image ⊆ T.1)
    (hT : T.1 ⊆ R.pieceRange c.m) :
    R.cmap S c φ ≫ R.ιL c.m = R.ymap S T (φ.comp (rho c T.rep (rep_image_of_subset hcT))) := by
  let D := R.pieceDomain c.m
  have hT' : range ((atlas R).chart T) ⊆ R.pieceRange c.m := by
    change range (chartMap T) ⊆ _
    rw [range_chartMap]; exact hT
  let c' : (R.presentation.domain D).presentation.atlas.Index := ⟨T, hT'⟩
  have h1 : (R.pieceMap c.m).baseMap '' range ((R.atl c.m).chart c.i) ⊆
      range ((R.presentation.domain D).presentation.atlas.chart c') := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : R.ι c.m ((R.atl c.m).chart c.i x) ∈ range (chartMap T) := by
      rw [range_chartMap]; exact hcT ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  have h2 : (R.presentation.domainInclusion D).baseMap ''
      range ((R.presentation.domain D).presentation.atlas.chart c') ⊆
        range ((atlas R).chart T) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have e1 := SmallAffinoidSpectrum.chartMap_comp (A := presentationOf (R.Z c.m)) (R := S)
    c.i φ (R.pieceMap c.m) c' h1
  have e2 := SmallAffinoidSpectrum.chartMap_comp (A := R.presentation.domain D) (R := S)
    c' (φ.comp ((R.pieceMap c.m).pullback c.i c' h1)) (R.presentation.domainInclusion D) T h2
  have e3 : (R.presentation.domainInclusion D).pullback c' T h2 =
      BoundedAlgHom.id K T.rep.alg := (atlas R).restriction_id T subset_rfl
  have e4 : R.cmap S c φ ≫ R.ιL c.m = localizationFunctor.map
      ((SmallAffinoidSpectrum.chartMap.{u, u} S (B := presentationOf (R.Z c.m)) c.i φ ≫
        R.pieceMap c.m) ≫ R.presentation.domainInclusion D) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc]
    rfl
  rw [e4, e1, e2]
  refine congrArg (fun ψ => localizationFunctor.map
    (SmallAffinoidSpectrum.chartMap.{u, u} S (B := R.presentation) T ψ)) ?_
  ext a
  have ha : (R.presentation.domainInclusion D).pullback c' T h2 a = a :=
    congrArg (fun g => g a) e3
  change φ ((R.pieceMap c.m).pullback c.i c' h1
    ((R.presentation.domainInclusion D).pullback c' T h2 a)) =
      φ ((R.pieceMap c.m).pullback c.i c' h1 a)
  rw [ha]

/-! ## The domain of the relation between two pieces -/

variable (R) in
/-- The domain of the relation between two pieces, as an open analytic domain. -/
abbrev domW (m n : R.M) : (presentationOf (R.Z m)).AnalyticDomain :=
  (presentationOf (R.Z m)).openDomain (R.domainSet m n) (R.isOpen_domainSet m n)

variable (R) in
/-- The inclusion of the domain of the relation. -/
abbrev nuW (m n : R.M) : domainObj (R.Z m) (R.domW m n) ⟶ R.Z m := domainι (R.Z m) (R.domW m n)

theorem nuW_mem (m n : R.M) (x : localizedSpaceFunctor.obj (domainObj (R.Z m) (R.domW m n))) :
    localizedSpaceFunctor.map (R.nuW m n) x ∈ R.domainSet m n := by
  rw [domainι_apply]; exact x.property

variable (R) in
/-- The transfer of the domain of the relation to the other piece. -/
def tauW (m n : R.M) : domainObj (R.Z m) (R.domW m n) ⟶ R.Z n :=
  transfer n (R.nuW m n) (nuW_mem m n)

theorem rel_nuW_tauW (m n : R.M) : R.Rel (R.nuW m n) (R.tauW m n) :=
  rel_transfer n _ _

/-- The small chart spectra of the domain of the relation are charts of the piece. -/
theorem smallChart_nuW (m n : R.M)
    (j : ((presentationOf (R.Z m)).domain (R.domW m n)).presentation.atlas.Index) :
    localizationFunctor.map
        (((presentationOf (R.Z m)).domain (R.domW m n)).smallChartSpectrumInclusion j) ≫
      R.nuW m n = incl (⟨m, j.1⟩ : R.PieceChart) := by
  let A := (presentationOf (R.Z m)).domain (R.domW m n)
  let D := R.domW m n
  have h2 : ((presentationOf (R.Z m)).domainInclusion D).baseMap ''
      range (A.presentation.atlas.chart j) ⊆ range ((R.atl m).chart j.1) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have e2 := SmallAffinoidSpectrum.chartMap_comp (A := A) (R := (R.atl m).algebra j.1)
    j (BoundedAlgHom.id K _) ((presentationOf (R.Z m)).domainInclusion D) j.1 h2
  have e3 : ((presentationOf (R.Z m)).domainInclusion D).pullback j j.1 h2 =
      BoundedAlgHom.id K ((R.atl m).algebra j.1) := (R.atl m).restriction_id j.1 _
  have e4 : localizationFunctor.map (A.smallChartSpectrumInclusion j) ≫ R.nuW m n =
      localizationFunctor.map (SmallAffinoidSpectrum.chartMap.{u, u} ((R.atl m).algebra j.1)
        (B := A) j (BoundedAlgHom.id K _) ≫ (presentationOf (R.Z m)).domainInclusion D) := by
    rw [Functor.map_comp]; rfl
  rw [e4, e2]
  refine congrArg (fun ψ => localizationFunctor.map
    (SmallAffinoidSpectrum.chartMap.{u, u} ((R.atl m).algebra j.1)
      (B := presentationOf (R.Z m)) j.1 ψ)) ?_
  ext a
  have ha : ((presentationOf (R.Z m)).domainInclusion D).pullback j j.1 h2 a = a :=
    congrArg (fun g => g a) e3
  exact ha

variable (R) in
/-- Charts of the domain of the relation between `m` and `n` whose image lies in the image of a
chart of the piece `n`. -/
def CoverIndex (m n : R.M) : Type u :=
  {p : ((presentationOf (R.Z m)).domain (R.domW m n)).presentation.atlas.Index ×
      (R.atl n).Index // (⟨m, p.1.1⟩ : R.PieceChart).image ⊆ (⟨n, p.2⟩ : R.PieceChart).image}

theorem mem_domainSet_of_mem_image {m : R.M} (d : R.PieceChart)
    {w : localizedSpaceFunctor.obj (R.Z m)} (hw : R.ι m w ∈ d.image) :
    w ∈ R.domainSet m d.m := by
  rw [← preimage_range_ι]
  obtain ⟨w', -, h⟩ := hw
  exact ⟨w', h⟩

theorem coverIndex_locallyRefines (m n : R.M) :
    AtlasTopology.LocallyRefines
      (range (fun k : R.CoverIndex m n =>
        range (((presentationOf (R.Z m)).domain (R.domW m n)).presentation.atlas.chart k.1.1)))
      {univ} := by
  rintro _ hU x -
  rw [mem_singleton_iff] at hU
  subst hU
  have hx : (x.val : localizedSpaceFunctor.obj (R.Z m)) ∈ R.domainSet m n := x.property
  rw [← preimage_range_ι] at hx
  obtain ⟨z', hz'⟩ := hx
  obtain ⟨σn, hσf, hστ, hσy, hσn⟩ := (R.atl n).isNet_chartFamily.1 z'
  have hfin : Finite σn := hσf.to_subtype
  have hj : ∀ V : σn, ∃ j : (R.atl n).Index, range ((R.atl n).chart j) = V.1 :=
    fun V => hστ V.2
  choose J hJ using hj
  let E : σn → Set (presentationOf (R.Z m)).presentation.space := fun V =>
    {w | R.ι m w ∈ (⟨n, J V⟩ : R.PieceChart).image}
  have hzE : ∀ V : σn, (x.val : (presentationOf (R.Z m)).presentation.space) ∈ E V := by
    intro V
    show R.ι m x.val ∈ (⟨n, J V⟩ : R.PieceChart).image
    rw [← hz']
    refine ⟨z', ?_, rfl⟩
    change z' ∈ range ((R.atl n).chart (J V))
    rw [hJ V]
    exact hσy V.1 V.2
  have hloc : ∀ V : σn, ∃ σ : Set (Set (presentationOf (R.Z m)).presentation.space),
      σ.Finite ∧ σ ⊆ range (fun i => range ((R.atl m).chart i)) ∧
        (∀ W ∈ σ, W ⊆ E V ∧ x.val ∈ W) ∧ ⋃₀ σ ∈ 𝓝[E V] x.val := fun V =>
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
      (isOriginalChartDomain_preimage_image m ⟨n, J V⟩) _ (mem_singleton _) _ (hzE V)
  choose σ hσfin hσsub hσmem hσnhds using hloc
  refine ⟨⋃ V : σn, (fun W => (Subtype.val ⁻¹' W :
      Set ((presentationOf (R.Z m)).domain (R.domW m n)).presentation.space)) '' σ V,
    finite_iUnion fun V => (hσfin V).image _, ?_, ?_, ?_⟩
  · rintro _ hW0
    obtain ⟨V, ⟨W, hW, rfl⟩⟩ := mem_iUnion.mp hW0
    obtain ⟨i, hi⟩ := hσsub V hW
    have hi' : range ((R.atl m).chart i) = W := hi
    have hiW : range ((R.atl m).chart i) ⊆ R.domainSet m n := by
      intro w hw
      have hw' : w ∈ W := hi' ▸ hw
      exact mem_domainSet_of_mem_image ⟨n, J V⟩ ((hσmem V W hW).1 hw')
    let c : ((presentationOf (R.Z m)).domain (R.domW m n)).presentation.atlas.Index := ⟨i, hiW⟩
    have hcd : (⟨m, c.1⟩ : R.PieceChart).image ⊆ (⟨n, J V⟩ : R.PieceChart).image := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : w ∈ W := hi' ▸ hw
      exact (hσmem V W hW).1 hw'
    exact ⟨⟨(c, J V), hcd⟩, ((R.atl m).range_subspaceChart (R.domainSet m n) c).trans
      (congrArg (fun S => (Subtype.val ⁻¹' S :
        Set ((presentationOf (R.Z m)).domain (R.domW m n)).presentation.space)) hi')⟩
  · rintro _ hW0
    obtain ⟨V, ⟨W, hW, rfl⟩⟩ := mem_iUnion.mp hW0
    exact ⟨subset_univ _, (hσmem V W hW).2⟩
  · rw [nhdsWithin_univ]
    have hN : R.ι m ⁻¹' (R.ι n '' ⋃₀ σn) ∈ 𝓝 (x.val : localizedSpaceFunctor.obj (R.Z m)) := by
      apply (continuous_ι m).continuousAt.preimage_mem_nhds
      rw [← hz']
      exact (isOpenEmbedding_ι n).isOpenMap.image_mem_nhds hσn
    have hall : ∀ᶠ w in 𝓝 (x.val : (presentationOf (R.Z m)).presentation.space),
        ∀ V : σn, w ∈ E V → w ∈ ⋃₀ σ V :=
      Filter.eventually_all.mpr fun V => mem_nhdsWithin_iff_eventually.mp (hσnhds V)
    have hmain : (⋃ V : σn, ⋃₀ σ V) ∈ 𝓝 (x.val : (presentationOf (R.Z m)).presentation.space) := by
      filter_upwards [hN, hall] with w hwN hwall
      obtain ⟨w'', ⟨V, hV, hw''⟩, hww⟩ := hwN
      have hwE : w ∈ E ⟨V, hV⟩ := by
        show R.ι m w ∈ (⟨n, J ⟨V, hV⟩⟩ : R.PieceChart).image
        rw [← hww]
        refine ⟨w'', ?_, rfl⟩
        change w'' ∈ range ((R.atl n).chart (J ⟨V, hV⟩))
        rw [hJ ⟨V, hV⟩]
        exact hw''
      exact mem_iUnion.mpr ⟨⟨V, hV⟩, hwall ⟨V, hV⟩ hwE⟩
    have hpre := continuous_subtype_val.continuousAt.preimage_mem_nhds (x := x) hmain
    refine Filter.mem_of_superset hpre ?_
    intro y hy
    obtain ⟨V, hV⟩ := mem_iUnion.mp hy
    obtain ⟨W, hW, hyW⟩ := hV
    exact ⟨_, mem_iUnion.mpr ⟨V, ⟨W, hW, rfl⟩⟩, hyW⟩

/-- The domain of the relation and its transfer have the same composite into the glued
space. -/
theorem nuW_ιL (m n : R.M) : R.nuW m n ≫ R.ιL m = R.tauW m n ≫ R.ιL n := by
  apply localizedHom_ext_of_chartCover (A := (presentationOf (R.Z m)).domain (R.domW m n))
    (fun k : R.CoverIndex m n => k.1.1) (coverIndex_locallyRefines m n)
  intro k
  let c : R.PieceChart := ⟨m, k.1.1.1⟩
  let d : R.PieceChart := ⟨n, k.1.2⟩
  have hcd : c.image ⊆ d.image := k.2
  let sc := localizationFunctor.map
    (((presentationOf (R.Z m)).domain (R.domW m n)).smallChartSpectrumInclusion k.1.1)
  have h1 : sc ≫ R.nuW m n = incl c := smallChart_nuW m n k.1.1
  have h2 : sc ≫ R.tauW m n = R.cmap c.alg d (rho c d hcd) := by
    have r1 : R.Rel (incl c) (sc ≫ R.tauW m n) := by
      rw [← h1]; exact (rel_nuW_tauW m n).comp sc
    exact r1.unique (rel_rho c d hcd)
  let Tc : R.ChartImage := ⟨c.image, c, rfl⟩
  let Td : R.ChartImage := ⟨d.image, d, rfl⟩
  have e1 := cmap_ιL c.alg c (BoundedAlgHom.id K _) Tc subset_rfl (image_subset_pieceRange c)
  have e2 := cmap_ιL c.alg d (rho c d hcd) Td subset_rfl (image_subset_pieceRange d)
  have hTcd : range ((atlas R).chart Tc) ⊆ range ((atlas R).chart Td) := by
    change range (chartMap Tc) ⊆ range (chartMap Td)
    rw [range_chartMap, range_chartMap]
    exact hcd
  have e3 := SmallAffinoidSpectrum.chartMap_of_subset (B := R.presentation) c.alg Tc Td hTcd
    ((BoundedAlgHom.id K _).comp (rho c Tc.rep (rep_image_of_subset subset_rfl)))
  have hTT : Tc.rep.image ⊆ Td.rep.image := by
    rw [Tc.rep_image, Td.rep_image]; exact hcd
  have e4 : ((BoundedAlgHom.id K _).comp (rho c Tc.rep (rep_image_of_subset subset_rfl))).comp
        ((atlas R).restriction Tc Td hTcd) =
      (rho c d hcd).comp (rho d Td.rep (rep_image_of_subset subset_rfl)) := by
    rw [BoundedAlgHom.id_comp]
    exact (rho_comp c Tc.rep Td.rep _ hTT (hcd.trans (rep_image_of_subset subset_rfl))).symm.trans
      (rho_comp c d Td.rep hcd _ _)
  have lhs : (sc ≫ R.nuW m n) ≫ R.ιL m =
      R.ymap c.alg Td ((rho c d hcd).comp (rho d Td.rep (rep_image_of_subset subset_rfl))) := by
    rw [h1]
    refine e1.trans ?_
    rw [← e4]
    exact congrArg localizationFunctor.map e3
  have rhs : (sc ≫ R.tauW m n) ≫ R.ιL n =
      R.ymap c.alg Td ((rho c d hcd).comp (rho d Td.rep (rep_image_of_subset subset_rfl))) := by
    rw [h2]; exact e2
  rw [← Category.assoc, ← Category.assoc]
  exact lhs.trans rhs.symm

/-- Related morphisms into two pieces have the same composite into the glued space. -/
theorem Rel.ιL_eq {T : LocalizedCategory.{u, u, u} (K := K)} {m n : R.M}
    {f : T ⟶ R.Z m} {g : T ⟶ R.Z n} (h : R.Rel f g) : f ≫ R.ιL m = g ≫ R.ιL n := by
  obtain ⟨f', hf'⟩ := exists_domainLift (R.domW m n) f h.mem_domainSet
  have hg : g = f' ≫ R.tauW m n := by
    have r : R.Rel f (f' ≫ R.tauW m n) := by
      rw [← hf']; exact (rel_nuW_tauW m n).comp f'
    exact h.unique r
  rw [hg, ← hf', Category.assoc, Category.assoc, nuW_ιL]

theorem a_ιL_eq_b_ιL (m n : R.M) : R.a m n ≫ R.ιL m = R.b m n ≫ R.ιL n :=
  Rel.ιL_eq ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩

/-- The relation is the fibre product of two pieces over the glued space. -/
theorem isPullback_ιL (m n : R.M) : IsPullback (R.a m n) (R.b m n) (R.ιL m) (R.ιL n) := by
  have hex : ∀ s : PullbackCone (R.ιL m) (R.ιL n),
      ∃ l : s.pt ⟶ R.S m n, l ≫ R.a m n = s.fst := by
    intro s
    apply openImmersion.exists_lift (R.a_open m n)
    intro x
    have e := congrArg (fun φ => localizedSpaceFunctor.map φ x) s.condition
    simp only [Functor.map_comp, TopCat.comp_app] at e
    rw [ιL_apply, ιL_apply] at e
    have hx : localizedSpaceFunctor.map s.fst x ∈ R.ι m ⁻¹' range (R.ι n) := ⟨_, e.symm⟩
    rw [preimage_range_ι] at hx
    exact hx
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (a_ιL_eq_b_ιL m n)
    (fun s => Classical.choose (hex s)) (fun s => Classical.choose_spec (hex s)) ?_ ?_)
  · intro s
    have hl := Classical.choose_spec (hex s)
    have hrel : R.Rel s.fst (Classical.choose (hex s) ≫ R.b m n) := ⟨_, hl, rfl⟩
    have e := hrel.ιL_eq
    rw [s.condition] at e
    exact (openImmersion.mono' (openImmersion_ιL n)).right_cancellation _ _ e.symm
  · intro s l hl _
    exact (cancel_mono (R.a m n)).1 (hl.trans (Classical.choose_spec (hex s)).symm)

variable (R) in
/-- **Gluing of analytic spaces along open subspaces.** Gluing data in relation form have a
glued analytic space: the pieces map to it by open immersions, jointly surjectively on points,
and every relation space is the fibre product of the two pieces over it. -/
theorem exists_glued :
    ∃ (Y : LocalizedCategory.{u, u, u} (K := K)) (ι : ∀ m, R.Z m ⟶ Y),
      (∀ m, openImmersion (ι m)) ∧
      (∀ y : localizedSpaceFunctor.obj Y, ∃ m, y ∈ range (localizedSpaceFunctor.map (ι m))) ∧
      ∀ m n, IsPullback (R.a m n) (R.b m n) (ι m) (ι n) := by
  refine ⟨R.glued, R.ιL, openImmersion_ιL, fun y => ?_, isPullback_ιL⟩
  obtain ⟨m, z, hz⟩ := exists_ι_eq (R := R) y
  exact ⟨m, z, (ιL_apply m z).trans hz⟩

end Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation



