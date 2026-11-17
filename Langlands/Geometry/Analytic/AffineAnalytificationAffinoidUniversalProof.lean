import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidUniversalStatement

/-! # Proof: strong maps from affinoid spectra to an affine analytification -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory Set AffinoidAtlasPresentation PresentedAffinoidAlgebra AnalyticAffineSpace

namespace AffinoidUniversalComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

omit [CompleteSpace K] in
/-- The coordinates of a chart algebra are the images of the generators of `A`. -/
theorem coordinate_eq_algebraMap (m : ℕ) (t : Fin P.arity) :
    coordinate K (algebra K P m) t =
      PolynomialLocus.algebraMap P (polyradius K P.arity m) (P.map (MvPolynomial.X t)) := by
  rw [PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]

/-- The restrictions of the constructed atlas send coordinates to coordinates. -/
theorem atlas_restriction_coordinate (i j : (presentation K P).atlas.Index)
    (h : range ((presentation K P).atlas.chart i) ⊆ range ((presentation K P).atlas.chart j))
    (t : Fin P.arity) :
    (presentation K P).atlas.restriction i j h (coordinate K (algebra K P j.val) t) =
      coordinate K (algebra K P i.val) t :=
  PolynomialLocus.restriction_coordinate P _ _ _ t

/-- Two charts of the constructed atlas lie in a common chart. -/
theorem exists_common_chart (j j' : (presentation K P).atlas.Index) :
    ∃ q : (presentation K P).atlas.Index,
      range ((presentation K P).atlas.chart j) ⊆ range ((presentation K P).atlas.chart q) ∧
        range ((presentation K P).atlas.chart j') ⊆ range ((presentation K P).atlas.chart q) :=
  atlas_hasDirectedCharts K P j j'

/-! ## Strong maps into the constructed atlas -/

section Strong

variable {X : AffinoidAtlasPresentation.{u, u, 0} K}

/-- The coordinate values of the pullbacks of a strong map into the constructed atlas do
not depend on the admissible target chart. -/
theorem pullback_coordinate_eq (F : StrongHom X (presentation K P)) (i : X.atlas.Index)
    (j j' : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j))
    (h' : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j'))
    (t : Fin P.arity) :
    F.pullback i j h (coordinate K (algebra K P j.val) t) =
      F.pullback i j' h' (coordinate K (algebra K P j'.val) t) := by
  obtain ⟨q, hjq, hj'q⟩ := exists_common_chart P j j'
  have hq : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart q) :=
    h.trans hjq
  have c : F.pullback i q hq (coordinate K (algebra K P q.val) t) =
      F.pullback i j h (coordinate K (algebra K P j.val) t) := by
    rw [F.pullback_comp_restriction i j q hjq h hq]
    exact congrArg (F.pullback i j h) (atlas_restriction_coordinate P j q hjq t)
  have c' : F.pullback i q hq (coordinate K (algebra K P q.val) t) =
      F.pullback i j' h' (coordinate K (algebra K P j'.val) t) := by
    rw [F.pullback_comp_restriction i j' q hj'q h' hq]
    exact congrArg (F.pullback i j' h') (atlas_restriction_coordinate P j' q hj'q t)
  exact c.symm.trans c'

/-- A strong map into the constructed atlas is determined by the coordinate values of
one admissible pullback for each source chart. -/
theorem strongHom_eq_of_coordinate (F G : StrongHom X (presentation K P))
    (hcover : ∀ z : X.space, ∃ i, z ∈ range (X.atlas.chart i))
    (hp : ∀ i, ∃ (j : (presentation K P).atlas.Index)
      (hF : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j))
      (j' : (presentation K P).atlas.Index)
      (hG : G.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j')),
      ∀ t : Fin P.arity, F.pullback i j hF (coordinate K (algebra K P j.val) t) =
        G.pullback i j' hG (coordinate K (algebra K P j'.val) t)) :
    F = G := by
  have hpb : ∀ i, ∃ (q : (presentation K P).atlas.Index)
      (hF : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart q))
      (hG : G.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart q)),
      F.pullback i q hF = G.pullback i q hG := by
    intro i
    obtain ⟨j, hF, j', hG, h⟩ := hp i
    obtain ⟨q, hjq, hj'q⟩ := exists_common_chart P j j'
    have hFq : F.baseMap '' range (X.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart q) := hF.trans hjq
    have hGq : G.baseMap '' range (X.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart q) := hG.trans hj'q
    refine ⟨q, hFq, hGq, ?_⟩
    apply PresentedAffinoidAlgebra.hom_ext_coordinate
    intro t
    exact (pullback_coordinate_eq P F i q j hFq hF t).trans
      ((h t).trans (pullback_coordinate_eq P G i j' q hG hGq t))
  have hb : F.baseMap = G.baseMap := by
    ext z
    obtain ⟨i, y, rfl⟩ := hcover z
    obtain ⟨q, hF, hG, h⟩ := hpb i
    rw [← F.chart_comm i q hF y, ← G.chart_comm i q hG y, h]
  refine StrongHom.ext_of_directed (atlas_hasDirectedCharts K P) hb fun i => ?_
  obtain ⟨q, hF, hG, h⟩ := hpb i
  exact ⟨q, hF, h⟩

end Strong

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Two `K`-algebra maps out of a presented algebra agree if they agree on the
generators. -/
theorem algHom_ext_generators {B : Type w} [Semiring B] [Algebra K B] {φ ψ : A →ₐ[K] B}
    (h : ∀ t, φ (P.map (MvPolynomial.X t)) = ψ (P.map (MvPolynomial.X t))) : φ = ψ := by
  have hc : φ.comp P.map = ψ.comp P.map := MvPolynomial.algHom_ext h
  ext a
  obtain ⟨p, rfl⟩ := P.surjective a
  exact AlgHom.congr_fun hc p

variable {R : PresentedAffinoidAlgebra K}

/-- On coordinates, a pullback of a strong map out of the singleton atlas does not
depend on the admissible target chart (the coordinate-comparison lemma). -/
theorem pullback_coordinate_indep
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P))
    (j j' : (presentation K P).atlas.Index)
    (h : F.baseMap '' range
        ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart PUnit.unit) ⊆
      range ((presentation K P).atlas.chart j))
    (h' : F.baseMap '' range
        ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart PUnit.unit) ⊆
      range ((presentation K P).atlas.chart j'))
    (t : Fin P.arity) :
    F.pullback PUnit.unit j h (coordinate K (algebra K P j.val) t) =
      F.pullback PUnit.unit j' h' (coordinate K (algebra K P j'.val) t) :=
  pullback_coordinate_eq P F PUnit.unit j j' h h' t

/-- Assertion (1): every admissible pullback recovers `strongHomAlgHom`. -/
theorem pullback_algebraMap_eq
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P))
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range
        ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart PUnit.unit) ⊆
      range ((presentation K P).atlas.chart j))
    (a : A) :
    F.pullback PUnit.unit j h (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a) =
      strongHomAlgHom F a := by
  have e : (F.pullback PUnit.unit j h).toAlgHom.comp
      (PolynomialLocus.algebraMap P (polyradius K P.arity j.val)) = strongHomAlgHom F := by
    apply algHom_ext_generators P
    intro t
    have c1 := coordinate_eq_algebraMap P j.val t
    have c2 := coordinate_eq_algebraMap P (strongHomTarget F).val t
    change F.pullback PUnit.unit j h
        (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) (P.map (MvPolynomial.X t))) =
      F.pullback PUnit.unit (strongHomTarget F) (strongHomTarget_spec F)
        (PolynomialLocus.algebraMap P (polyradius K P.arity (strongHomTarget F).val)
          (P.map (MvPolynomial.X t)))
    rw [← c1, ← c2]
    exact pullback_coordinate_indep P F j (strongHomTarget F) h (strongHomTarget_spec F) t
  exact AlgHom.congr_fun e a

/-- The selected pullback of `affinoidStrongHom` is `affinoidPullback`. -/
theorem affinoidStrongHom_pullback_selected (φ : A →ₐ[K] R) :
    (affinoidStrongHom K P R φ).pullback PUnit.unit (affinoidIndex K P R φ)
        ((affinoidAtlasHom K P R φ).image_chart_subset PUnit.unit) =
      affinoidPullback K P R φ :=
  StrongHom.ofDirected_pullback_selected (affinoidAtlasHom K P R φ)
    (atlas_hasDirectedCharts K P) PUnit.unit

/-- On coordinates, the selected pullback of `affinoidStrongHom` gives the generator
values. -/
theorem affinoidStrongHom_pullback_coordinate (φ : A →ₐ[K] R) (t : Fin P.arity) :
    (affinoidStrongHom K P R φ).pullback PUnit.unit (affinoidIndex K P R φ)
        ((affinoidAtlasHom K P R φ).image_chart_subset PUnit.unit)
        (coordinate K (algebra K P (affinoidIndex K P R φ).val) t) =
      φ (P.map (MvPolynomial.X t)) := by
  rw [affinoidStrongHom_pullback_selected,
    coordinate_eq_algebraMap P (affinoidIndex K P R φ).val t]
  exact affinoidPullback_algebraMap K P R φ _

/-- Assertion (2). -/
theorem strongHomAlgHom_affinoidStrongHom (φ : A →ₐ[K] R) :
    strongHomAlgHom (affinoidStrongHom K P R φ) = φ := by
  ext a
  rw [← pullback_algebraMap_eq P (affinoidStrongHom K P R φ) (affinoidIndex K P R φ)
    ((affinoidAtlasHom K P R φ).image_chart_subset PUnit.unit) a,
    affinoidStrongHom_pullback_selected]
  exact affinoidPullback_algebraMap K P R φ a

/-- The single chart of an affinoid spectrum covers it. -/
theorem singleton_cover
    (z : (PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).space) :
    ∃ i, z ∈ range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart i) :=
  ⟨PUnit.unit, z, rfl⟩

/-- Assertion (3). -/
theorem affinoidStrongHom_strongHomAlgHom
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P)) :
    affinoidStrongHom K P R (strongHomAlgHom F) = F := by
  apply strongHom_eq_of_coordinate P _ _ singleton_cover
  intro i
  refine ⟨affinoidIndex K P R (strongHomAlgHom F),
    (affinoidAtlasHom K P R (strongHomAlgHom F)).image_chart_subset PUnit.unit,
    strongHomTarget F, strongHomTarget_spec F, fun t => ?_⟩
  have c := coordinate_eq_algebraMap P (strongHomTarget F).val t
  refine (affinoidStrongHom_pullback_coordinate P (strongHomAlgHom F) t).trans ?_
  rw [c]
  exact (strongHomAlgHom_apply F _).symm

/-- Assertion (4). -/
theorem pointSeminorm_affinoidStrongHom (φ : A →ₐ[K] R) (x : BanachSpectrum R) (a : A) :
    pointSeminorm K P ((affinoidStrongHom K P R φ).baseMap x) a = x (φ a) := by
  change pointSeminorm K P (chart K P (affinoidLevel K P R φ)
    (BanachSpectrum.comap (affinoidChartMap K P R φ).toBoundedRingHom x)) a = _
  rw [pointSeminorm_chart, chartSeminorm_apply]
  change x (affinoidChartMap K P R φ (PolynomialLocus.algebraMap P _ a)) = _
  rw [affinoidChartMap_algebraMap]

/-- Assertion (5): naturality in the affinoid algebra. -/
theorem compOfDirected_strongAtlasMap {R' : PresentedAffinoidAlgebra K} (g : R ⟶ R')
    (φ : A →ₐ[K] R) :
    (PresentedAffinoidSpace.strongAtlasMap g.op).compOfDirected (affinoidStrongHom K P R φ)
        (PresentedAffinoidSpace.atlasPresentation_hasDirectedCharts (Opposite.op R))
        (atlas_hasDirectedCharts K P) =
      affinoidStrongHom K P R' (g.toAlgHom.comp φ) := by
  symm
  apply strongHom_eq_of_coordinate P _ _ singleton_cover
  intro i
  have hf : (PresentedAffinoidSpace.strongAtlasMap g.op).baseMap ''
      range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R')).atlas.chart i) ⊆
        range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart
          PUnit.unit) :=
    (PresentedAffinoidSpace.strongAtlasMap g.op).image_chart_top PUnit.unit
      (PresentedAffinoidSpace.atlasPresentation_top_contains _) i
  have hg := (affinoidAtlasHom K P R φ).image_chart_subset PUnit.unit
  have hc : ((PresentedAffinoidSpace.strongAtlasMap g.op).compOfDirected
        (affinoidStrongHom K P R φ)
        (PresentedAffinoidSpace.atlasPresentation_hasDirectedCharts (Opposite.op R))
        (atlas_hasDirectedCharts K P)).baseMap ''
      range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R')).atlas.chart i) ⊆
        range ((presentation K P).atlas.chart (affinoidIndex K P R φ)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg (mem_image_of_mem _ (hf (mem_image_of_mem _ hy)))
  refine ⟨affinoidIndex K P R' (g.toAlgHom.comp φ),
    (affinoidAtlasHom K P R' (g.toAlgHom.comp φ)).image_chart_subset PUnit.unit,
    affinoidIndex K P R φ, hc, fun t => ?_⟩
  refine (affinoidStrongHom_pullback_coordinate P (g.toAlgHom.comp φ) t).trans ?_
  rw [StrongHom.compOfDirected_pullback _ _ _ _ i PUnit.unit (affinoidIndex K P R φ) hf hg hc]
  change g.toAlgHom (φ (P.map (MvPolynomial.X t))) =
    (PresentedAffinoidSpace.strongAtlasMap g.op).pullback i PUnit.unit hf
      ((affinoidStrongHom K P R φ).pullback PUnit.unit (affinoidIndex K P R φ) hg
        (coordinate K (algebra K P (affinoidIndex K P R φ).val) t))
  rw [affinoidStrongHom_pullback_coordinate P φ t, PresentedAffinoidSpace.strongAtlasMap_pullback]
  rfl

/-- Assertion (6): naturality in the presented algebra. -/
theorem compOfDirected_strongHom {B : Type w} [CommRing B] [Algebra K B]
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B) (ψ : B →ₐ[K] R) :
    (affinoidStrongHom K Q R ψ).compOfDirected (strongHom K P Q f)
        (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P) =
      affinoidStrongHom K P R (ψ.comp f) := by
  symm
  apply strongHom_eq_of_coordinate P _ _ singleton_cover
  intro i
  have hf : (affinoidStrongHom K Q R ψ).baseMap ''
      range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart i) ⊆
        range ((presentation K Q).atlas.chart (affinoidIndex K Q R ψ)) :=
    (affinoidAtlasHom K Q R ψ).image_chart_subset i
  have hg := (atlasHom K P Q f).image_chart_subset (affinoidIndex K Q R ψ)
  have hc : ((affinoidStrongHom K Q R ψ).compOfDirected (strongHom K P Q f)
        (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P)).baseMap ''
      range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart i) ⊆
        range ((presentation K P).atlas.chart (indexMap K P Q f (affinoidIndex K Q R ψ))) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg (mem_image_of_mem _ (hf (mem_image_of_mem _ hy)))
  refine ⟨affinoidIndex K P R (ψ.comp f),
    (affinoidAtlasHom K P R (ψ.comp f)).image_chart_subset PUnit.unit,
    indexMap K P Q f (affinoidIndex K Q R ψ), hc, fun t => ?_⟩
  refine (affinoidStrongHom_pullback_coordinate P (ψ.comp f) t).trans ?_
  rw [StrongHom.compOfDirected_pullback _ _ _ _ i (affinoidIndex K Q R ψ)
    (indexMap K P Q f (affinoidIndex K Q R ψ)) hf hg hc]
  have hs : (strongHom K P Q f).pullback (affinoidIndex K Q R ψ)
      (indexMap K P Q f (affinoidIndex K Q R ψ)) hg = pullback K P Q f (affinoidIndex K Q R ψ) :=
    StrongHom.ofDirected_pullback_selected (atlasHom K P Q f) (atlas_hasDirectedCharts K P)
      (affinoidIndex K Q R ψ)
  have hr : (affinoidStrongHom K Q R ψ).pullback i (affinoidIndex K Q R ψ) hf =
      affinoidPullback K Q R ψ :=
    StrongHom.ofDirected_pullback_selected (affinoidAtlasHom K Q R ψ)
      (atlas_hasDirectedCharts K Q) i
  change ψ (f (P.map (MvPolynomial.X t))) =
    (affinoidStrongHom K Q R ψ).pullback i (affinoidIndex K Q R ψ) hf
      ((strongHom K P Q f).pullback (affinoidIndex K Q R ψ)
        (indexMap K P Q f (affinoidIndex K Q R ψ)) hg
        (coordinate K (algebra K P (indexMap K P Q f (affinoidIndex K Q R ψ)).val) t))
  rw [hs, hr, coordinate_eq_algebraMap P _ t, pullback_algebraMap]
  exact (affinoidPullback_algebraMap K Q R ψ _).symm

end AffinoidUniversalComparison

open AffinoidUniversalComparison in
/-- Strong maps from affinoid spectra satisfy the affine analytification universal property. -/
theorem affineAnalytificationAffinoidUniversal :
    AffineAnalytificationAffinoidUniversalStatement.{u, v, w} := by
  intro K _ _ _ A _ _ P
  exact ⟨fun _ F j h a => pullback_algebraMap_eq P F j h a,
    fun _ φ => strongHomAlgHom_affinoidStrongHom P φ,
    fun _ F => affinoidStrongHom_strongHomAlgHom P F,
    fun _ φ x a => pointSeminorm_affinoidStrongHom P φ x a,
    fun _ _ g φ => compOfDirected_strongAtlasMap P g φ,
    fun _ _ _ Q f _ ψ => compOfDirected_strongHom P Q f ψ⟩

end Langlands.Analytic.AffineAnalytification
