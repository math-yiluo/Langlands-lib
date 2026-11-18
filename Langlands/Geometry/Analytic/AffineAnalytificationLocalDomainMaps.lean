import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidMap
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.AnalytificationCenter

/-! # Bounded maps out of local-domain algebras of a polynomial-locus analytification -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.LocalDomainMaps

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- The coordinates of a chart algebra are the images of the generators of `A`. -/
theorem coordinate_eq_algebraMap (m : ℕ) (t : Fin P.arity) :
    coordinate K (algebra K P m) t =
      PolynomialLocus.algebraMap P (polyradius K P.arity m) (P.map (MvPolynomial.X t)) := by
  rw [PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]

/-- Two bounded maps out of a chart algebra agree once they agree on the image of `A`. -/
theorem chart_hom_ext {R : PresentedAffinoidAlgebra K} (m : ℕ)
    (β β' : BoundedAlgHom K (algebra K P m) R)
    (h : ∀ a : A, β (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) =
      β' (PolynomialLocus.algebraMap P (polyradius K P.arity m) a)) : β = β' := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  exact (congrArg β (coordinate_eq_algebraMap P m t)).trans
    ((h _).trans (congrArg β' (coordinate_eq_algebraMap P m t)).symm)

theorem comap_comp {R S T : PresentedAffinoidAlgebra K} (β : BoundedAlgHom K R S)
    (γ : BoundedAlgHom K S T) (x : BanachSpectrum T) :
    BanachSpectrum.comap (γ.comp β).toBoundedRingHom x =
      BanachSpectrum.comap β.toBoundedRingHom (BanachSpectrum.comap γ.toBoundedRingHom x) :=
  BanachSpectrum.ext fun _ => rfl

variable [CompleteSpace K]

omit [CompleteSpace K] in
theorem restriction_algebraMap {m k : ℕ} (h : m ≤ k) (a : A) :
    restriction K P h (PolynomialLocus.algebraMap P (polyradius K P.arity k) a) =
      PolynomialLocus.algebraMap P (polyradius K P.arity m) a :=
  PolynomialLocus.restriction_algebraMap P _ _ _ a

/-- The point of the analytification given by a bounded map out of a chart algebra
depends only on its values on `A`. -/
theorem chart_comap_eq_affinoidBaseMap {R : PresentedAffinoidAlgebra K} (m : ℕ)
    (γ : BoundedAlgHom K (algebra K P m) R) (α : A →ₐ[K] R)
    (hγ : ∀ a, γ (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) = α a)
    (x : BanachSpectrum R) :
    chart K P m (BanachSpectrum.comap γ.toBoundedRingHom x) =
      affinoidBaseMap K P R α x := by
  have hm : m ≤ max m (affinoidLevel K P R α) := le_max_left _ _
  have hl : affinoidLevel K P R α ≤ max m (affinoidLevel K P R α) := le_max_right _ _
  have he : γ.comp (restriction K P hm) =
      (affinoidChartMap K P R α).comp (restriction K P hl) := by
    apply chart_hom_ext P
    intro a
    rw [BoundedAlgHom.comp_apply, BoundedAlgHom.comp_apply, restriction_algebraMap,
      restriction_algebraMap, hγ, affinoidChartMap_algebraMap]
  rw [affinoidBaseMap_apply, ← chart_pull K P hm, ← chart_pull K P hl]
  have e2 := congrArg (fun ψ : BoundedAlgHom K (algebra K P (max m (affinoidLevel K P R α))) R =>
    chart K P (max m (affinoidLevel K P R α)) (BanachSpectrum.comap ψ.toBoundedRingHom x)) he
  simp only [comap_comp] at e2
  exact e2

/-- The seminorm of the image of a spectrum point is the point composed with `α`. -/
theorem pointSeminorm_affinoidBaseMap (R : PresentedAffinoidAlgebra K) (α : A →ₐ[K] R)
    (x : BanachSpectrum R) (a : A) :
    pointSeminorm K P (affinoidBaseMap K P R α x) a = x (α a) := by
  rw [affinoidBaseMap_apply, pointSeminorm_chart, chartSeminorm_apply]
  change x (affinoidChartMap K P R α _) = _
  rw [affinoidChartMap_algebraMap]

/-- The kernel of the image of a spectrum point is the preimage of its kernel. -/
theorem kernel_affinoidBaseMap (R : PresentedAffinoidAlgebra K) (α : A →ₐ[K] R)
    (x : BanachSpectrum R) :
    kernel K P (affinoidBaseMap K P R α x) = (BanachSpectrum.kernel x).comap α := by
  ext a
  rw [mem_kernel, pointSeminorm_affinoidBaseMap, Ideal.mem_comap]
  rfl

/-- Naturality of the affinoid base maps in the affinoid algebra. -/
theorem affinoidBaseMap_comp_left {R R' : PresentedAffinoidAlgebra K} (α : A →ₐ[K] R)
    (ρ : BoundedAlgHom K R R') (x : BanachSpectrum R') :
    affinoidBaseMap K P R' (ρ.toAlgHom.comp α) x =
      affinoidBaseMap K P R α (BanachSpectrum.comap ρ.toBoundedRingHom x) := by
  rw [← chart_comap_eq_affinoidBaseMap P (affinoidLevel K P R α)
    (ρ.comp (affinoidChartMap K P R α)) (ρ.toAlgHom.comp α) (fun a => by
      rw [BoundedAlgHom.comp_apply, affinoidChartMap_algebraMap]
      rfl) x, comap_comp]
  rfl

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)

/-- Naturality of the affinoid base maps in the affine algebra. -/
theorem baseMap_affinoidBaseMap (f : A →ₐ[K] B) (R : PresentedAffinoidAlgebra K)
    (β : B →ₐ[K] R) (x : BanachSpectrum R) :
    baseMap K P Q f (affinoidBaseMap K Q R β x) = affinoidBaseMap K P R (β.comp f) x := by
  rw [affinoidBaseMap_apply, baseMap_chart, ← comap_comp]
  apply chart_comap_eq_affinoidBaseMap
  intro a
  rw [BoundedAlgHom.comp_apply, chartMap_algebraMap, affinoidChartMap_algebraMap]
  rfl

/-- A `K`-algebra map from `A` to an affinoid algebra whose spectrum lands in the
`m`-th polydisc extends boundedly to the `m`-th chart algebra. -/
theorem exists_chart_lift (m : ℕ) (R : PresentedAffinoidAlgebra K) (α : A →ₐ[K] R)
    (hα : ∀ x, affinoidBaseMap K P R α x ∈ range (chart K P m)) :
    ∃ ψ : BoundedAlgHom K (algebra K P m) R,
      ∀ a, ψ (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) = α a := by
  have hm : m ≤ max m (affinoidLevel K P R α) := le_max_left _ _
  have hl : affinoidLevel K P R α ≤ max m (affinoidLevel K P R α) := le_max_right _ _
  have hφ : HasImageIn K ((affinoidChartMap K P R α).comp (restriction K P hl))
      (range (BanachSpectrum.comap (restriction K P hm).toBoundedRingHom)) := by
    intro x
    obtain ⟨y, hy⟩ := hα x
    refine ⟨y, (isClosedEmbedding_chart K P (max m (affinoidLevel K P R α))).injective ?_⟩
    have h1 : chart K P (max m (affinoidLevel K P R α))
        (BanachSpectrum.comap (restriction K P hm).toBoundedRingHom y) = chart K P m y :=
      chart_pull K P hm y
    have h2 : chart K P (max m (affinoidLevel K P R α))
        (BanachSpectrum.comap (restriction K P hl).toBoundedRingHom
          (BanachSpectrum.comap (affinoidChartMap K P R α).toBoundedRingHom x)) =
        affinoidBaseMap K P R α x :=
      chart_pull K P hl _
    rw [h1, hy, comap_comp, h2]
  obtain ⟨ψ, hψ, -⟩ := (represents_restriction K P hm).2.2 R _ hφ
  refine ⟨ψ, fun a => ?_⟩
  have e := congrArg (fun ψ : BoundedAlgHom K (algebra K P (max m (affinoidLevel K P R α))) R =>
    ψ (PolynomialLocus.algebraMap P (polyradius K P.arity (max m (affinoidLevel K P R α))) a)) hψ
  simp only [BoundedAlgHom.comp_apply, restriction_algebraMap,
    affinoidChartMap_algebraMap] at e
  exact e

/-! ## Affinoid domains of the chart algebras -/

section Domain

variable {m : ℕ} (D : Domain K (algebra K P m))

/-- The coordinate-algebra map into the algebra of an affinoid domain of a chart algebra. -/
def domainAlgebraMap : A →ₐ[K] D.algebra :=
  D.baseMap.toAlgHom.comp (PolynomialLocus.algebraMap P (polyradius K P.arity m))

theorem domainAlgebraMap_apply (a : A) :
    domainAlgebraMap P D a =
      D.baseMap (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) :=
  rfl

/-- Bounded maps out of a domain algebra are determined on `A`. -/
theorem domain_hom_ext {R : PresentedAffinoidAlgebra K} (β β' : BoundedAlgHom K D.algebra R)
    (h : ∀ a, β (domainAlgebraMap P D a) = β' (domainAlgebraMap P D a)) : β = β' := by
  have hc : β.comp D.baseMap = β'.comp D.baseMap :=
    chart_hom_ext P m _ _ h
  exact (D.represents.2.2 R (β'.comp D.baseMap) (fun x => by
    rw [comap_comp]
    exact D.represents.hasImageIn _)).unique hc rfl

/-- The point of the analytification given by a bounded map out of a domain algebra
is the affinoid base map of its restriction to `A`. -/
theorem chart_spectrumMap_comap {R : PresentedAffinoidAlgebra K}
    (β : BoundedAlgHom K D.algebra R) (x : BanachSpectrum R) :
    chart K P m (D.spectrumMap (BanachSpectrum.comap β.toBoundedRingHom x)) =
      affinoidBaseMap K P R (β.toAlgHom.comp (domainAlgebraMap P D)) x := by
  have h := chart_comap_eq_affinoidBaseMap P m (β.comp D.baseMap)
    (β.toAlgHom.comp (domainAlgebraMap P D)) (fun _ => rfl) x
  rw [comap_comp] at h
  exact h

/-- The points of a domain algebra are sent by its coordinate map to its locus. -/
theorem affinoidBaseMap_domainAlgebraMap (x : BanachSpectrum D.algebra) :
    affinoidBaseMap K P D.algebra (domainAlgebraMap P D) x = chart K P m (D.spectrumMap x) := by
  have h := chart_spectrumMap_comap P D (BoundedAlgHom.id K D.algebra) x
  exact h.symm.trans (congrArg (fun y => chart K P m (D.spectrumMap y))
    (BanachSpectrum.ext fun _ => rfl))

/-- Existence half of the universal property of a domain algebra: a `K`-algebra map
from `A` to an affinoid algebra whose spectrum lands in the image of the locus
extends boundedly. -/
theorem exists_domain_lift (R : PresentedAffinoidAlgebra K)
    (α : A →ₐ[K] R) (hα : ∀ x, affinoidBaseMap K P R α x ∈ chart K P m '' D.locus) :
    ∃ β : BoundedAlgHom K D.algebra R, β.toAlgHom.comp (domainAlgebraMap P D) = α := by
  obtain ⟨ψ, hψ⟩ := exists_chart_lift P m R α (fun x => by
    obtain ⟨y, -, hy⟩ := hα x
    exact ⟨y, hy⟩)
  have hD : HasImageIn K ψ D.locus := by
    intro x
    obtain ⟨y, hy, hyx⟩ := hα x
    have e : BanachSpectrum.comap ψ.toBoundedRingHom x = y :=
      (isClosedEmbedding_chart K P m).injective
        ((chart_comap_eq_affinoidBaseMap P m ψ α hψ x).trans hyx.symm)
    rw [e]
    exact hy
  obtain ⟨β, hβ, -⟩ := D.represents.2.2 R ψ hD
  refine ⟨β, AlgHom.ext fun a => ?_⟩
  rw [AlgHom.comp_apply, domainAlgebraMap_apply, ← hψ a, ← hβ]
  rfl

end Domain

/-! ## Local domains of the polynomial-locus atlas -/

/-- The coordinate-algebra map into the algebra of a local domain of the atlas. -/
def localAlgebraMap (L : LocalDomain (atlas K P)) : A →ₐ[K] L.algebra :=
  domainAlgebraMap (m := L.index.val) P L.domain

/-- Bounded maps out of a local-domain algebra are determined on `A`. -/
theorem localDomain_hom_ext (L : LocalDomain (atlas K P)) {R : PresentedAffinoidAlgebra K}
    (β β' : BoundedAlgHom K L.algebra R)
    (h : ∀ a, β (localAlgebraMap P L a) = β' (localAlgebraMap P L a)) : β = β' :=
  domain_hom_ext (m := L.index.val) P L.domain β β' h

/-- The point of the ambient analytification given by a bounded map out of a local-domain
algebra is the affinoid base map of its restriction to `A`. -/
theorem ambientMap_comap (L : LocalDomain (atlas K P)) {R : PresentedAffinoidAlgebra K}
    (β : BoundedAlgHom K L.algebra R) (x : BanachSpectrum R) :
    L.ambientMap (BanachSpectrum.comap β.toBoundedRingHom x) =
      affinoidBaseMap K P R (β.toAlgHom.comp (localAlgebraMap P L)) x :=
  chart_spectrumMap_comap (m := L.index.val) P L.domain β x

/-- The points of a local-domain algebra are sent by its coordinate map to its locus. -/
theorem affinoidBaseMap_localAlgebraMap (L : LocalDomain (atlas K P))
    (x : BanachSpectrum L.algebra) :
    affinoidBaseMap K P L.algebra (localAlgebraMap P L) x = L.ambientMap x :=
  affinoidBaseMap_domainAlgebraMap (m := L.index.val) P L.domain x

/-- Existence half of the universal property of a local-domain algebra. -/
theorem exists_localDomain_lift (L : LocalDomain (atlas K P)) (R : PresentedAffinoidAlgebra K)
    (α : A →ₐ[K] R) (hα : ∀ x, affinoidBaseMap K P R α x ∈ L.locus) :
    ∃ β : BoundedAlgHom K L.algebra R, β.toAlgHom.comp (localAlgebraMap P L) = α :=
  exists_domain_lift (m := L.index.val) P L.domain R α hα

/-! ## Compatibility with inclusions of local domains and with induced maps -/

theorem atlas_restriction_algebraMap (i j : ChartIndex K P)
    (h : Set.range ((atlas K P).chart i) ⊆ Set.range ((atlas K P).chart j)) (a : A) :
    (atlas K P).restriction i j h (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a) =
      PolynomialLocus.algebraMap P (polyradius K P.arity i.val) a :=
  restriction_algebraMap P ((selected_range_subset_iff K P i j).1 h) a

/-- The bounded restriction of an inclusion of local domains is compatible with the
coordinate-algebra maps. -/
theorem inclusion_localAlgebraMap {U V : LocalDomain (atlas K P)} (f : U ⟶ V) (a : A) :
    f.restriction (localAlgebraMap P V a) = localAlgebraMap P U a := by
  obtain ⟨q, hUq, hVq⟩ : ∃ q : ChartIndex K P,
      Set.range ((atlas K P).chart U.index) ⊆ Set.range ((atlas K P).chart q) ∧
        Set.range ((atlas K P).chart V.index) ⊆ Set.range ((atlas K P).chart q) :=
    atlas_hasDirectedCharts K P U.index V.index
  have hU : U.locus ⊆ Set.range ((atlas K P).chart q) :=
    (Set.image_subset_range _ _).trans hUq
  have hV : V.locus ⊆ Set.range ((atlas K P).chart q) :=
    (Set.image_subset_range _ _).trans hVq
  have e := f.comp_chart q hU hV
  rw [(atlas K P).domainChartRestriction_of_chartSubset V.index q V.domain hV hVq,
    (atlas K P).domainChartRestriction_of_chartSubset U.index q U.domain hU hUq] at e
  have e2 : f.restriction (V.domain.baseMap ((atlas K P).restriction V.index q hVq
        (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a))) =
      U.domain.baseMap ((atlas K P).restriction U.index q hUq
        (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) :=
    congrArg (fun ψ : BoundedAlgHom K ((atlas K P).algebra q) U.algebra =>
      ψ (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) e
  rw [atlas_restriction_algebraMap P V.index q hVq a,
    atlas_restriction_algebraMap P U.index q hUq a] at e2
  exact e2

/-- The bounded pullbacks of the strong map induced by `φ` are compatible with the
coordinate-algebra maps and `φ`. -/
theorem strongHom_pullback_algebraMap (φ : A →ₐ[K] B) (i : ChartIndex K Q)
    (j : ChartIndex K P)
    (h : (strongHom K P Q φ).baseMap '' Set.range ((presentation K Q).atlas.chart i) ⊆
      Set.range ((presentation K P).atlas.chart j)) (a : A) :
    (strongHom K P Q φ).pullback i j h
        (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val) (φ a) := by
  obtain ⟨q, hjq, hiq⟩ : ∃ q : ChartIndex K P,
      Set.range ((atlas K P).chart j) ⊆ Set.range ((atlas K P).chart q) ∧
        Set.range ((atlas K P).chart (indexMap K P Q φ i)) ⊆ Set.range ((atlas K P).chart q) :=
    atlas_hasDirectedCharts K P j (indexMap K P Q φ i)
  have hq : (strongHom K P Q φ).baseMap '' Set.range ((presentation K Q).atlas.chart i) ⊆
      Set.range ((presentation K P).atlas.chart q) := h.trans hjq
  have e3 : ((strongHom K P Q φ).pullback i j h).comp
        ((presentation K P).atlas.restriction j q hjq) =
      (pullback K P Q φ i).comp
        ((presentation K P).atlas.restriction (indexMap K P Q φ i) q hiq) := by
    rw [← (strongHom K P Q φ).pullback_comp_restriction i j q hjq h hq,
      (strongHom K P Q φ).pullback_comp_restriction i (indexMap K P Q φ i) q hiq
        ((atlasHom K P Q φ).image_chart_subset i) hq]
    congr 1
    exact AffinoidAtlasPresentation.StrongHom.ofDirected_pullback_selected
      (atlasHom K P Q φ) (atlas_hasDirectedCharts K P) i
  have e4 : (strongHom K P Q φ).pullback i j h ((atlas K P).restriction j q hjq
        (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) =
      pullback K P Q φ i ((atlas K P).restriction (indexMap K P Q φ i) q hiq
        (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) :=
    congrArg (fun ψ : BoundedAlgHom K ((presentation K P).atlas.algebra q)
      ((presentation K Q).atlas.algebra i) =>
        ψ (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) e3
  rw [atlas_restriction_algebraMap P j q hjq a,
    atlas_restriction_algebraMap P (indexMap K P Q φ i) q hiq a] at e4
  exact e4.trans (pullback_algebraMap K P Q φ i a)

/-- The bounded pullbacks between local domains of the strong map induced by `φ` are
compatible with the coordinate-algebra maps and `φ`. -/
theorem localDomainPullback_localAlgebraMap (φ : A →ₐ[K] B)
    (U : LocalDomain (presentation K Q).atlas) (V : LocalDomain (presentation K P).atlas)
    (h : (strongHom K P Q φ).baseMap '' U.locus ⊆ V.locus) (a : A) :
    (strongHom K P Q φ).localDomainPullback U V h (localAlgebraMap P V a) =
      localAlgebraMap Q U (φ a) := by
  obtain ⟨j0, hj0⟩ := (strongHom K P Q φ).target_exists U.index
  obtain ⟨q, hVq, hj0q⟩ : ∃ q : ChartIndex K P,
      Set.range ((atlas K P).chart V.index) ⊆ Set.range ((atlas K P).chart q) ∧
        Set.range ((atlas K P).chart j0) ⊆ Set.range ((atlas K P).chart q) :=
    atlas_hasDirectedCharts K P V.index j0
  have hVV' : V.locus ⊆ ((presentation K P).atlas.originalLocalDomain q).locus := by
    intro z hz
    obtain ⟨x, hx⟩ := hVq (Set.image_subset_range _ _ hz)
    show z ∈ (presentation K P).atlas.chart q '' Set.univ
    exact ⟨x, Set.mem_univ _, hx⟩
  have hU' : (strongHom K P Q φ).baseMap '' U.locus ⊆
      ((presentation K P).atlas.originalLocalDomain q).locus := h.trans hVV'
  have hparent : (strongHom K P Q φ).baseMap ''
      Set.range ((presentation K Q).atlas.chart U.index) ⊆
      Set.range ((presentation K P).atlas.chart q) := hj0.trans hj0q
  have e1 := (strongHom K P Q φ).localDomainPullback_target U
    (LocalDomain.Inclusion.ofSubset V _ hVV') h hU'
  have e2 : ((strongHom K P Q φ).localDomainPullback U
        ((presentation K P).atlas.originalLocalDomain q) hU').comp
        ((presentation K P).atlas.originalLocalDomain q).domain.baseMap =
      U.domain.baseMap.comp ((strongHom K P Q φ).pullback U.index q hparent) :=
    ((strongHom K P Q φ).localDomainPullback_comp_baseMap U _ hU').trans
      ((strongHom K P Q φ).localChartPullback_of_parent_admissible
        (strongHom_hasCoherentPullbacks K P Q φ) U q hparent _)
  have e3 : (strongHom K P Q φ).localDomainPullback U
        ((presentation K P).atlas.originalLocalDomain q) hU'
        (localAlgebraMap P ((presentation K P).atlas.originalLocalDomain q) a) =
      U.domain.baseMap ((strongHom K P Q φ).pullback U.index q hparent
        (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) :=
    congrArg (fun ψ : BoundedAlgHom K ((presentation K P).atlas.algebra q) U.algebra =>
      ψ (PolynomialLocus.algebraMap P (polyradius K P.arity q.val) a)) e2
  have e5 := strongHom_pullback_algebraMap P Q φ U.index q hparent a
  calc (strongHom K P Q φ).localDomainPullback U V h (localAlgebraMap P V a)
      = (strongHom K P Q φ).localDomainPullback U V h
          ((LocalDomain.Inclusion.ofSubset V _ hVV').restriction
            (localAlgebraMap P ((presentation K P).atlas.originalLocalDomain q) a)) := by
        rw [inclusion_localAlgebraMap P (LocalDomain.Inclusion.ofSubset V _ hVV') a]
    _ = (strongHom K P Q φ).localDomainPullback U
          ((presentation K P).atlas.originalLocalDomain q) hU'
          (localAlgebraMap P ((presentation K P).atlas.originalLocalDomain q) a) := by
        rw [← e1]
        rfl
    _ = localAlgebraMap Q U (φ a) := e3.trans (congrArg U.domain.baseMap e5)

/-- The bounded pullbacks of the saturated morphism induced by `φ` are compatible with the
coordinate-algebra maps of the chosen local domains and `φ`. -/
theorem saturatedHom_pullback_localAlgebraMap (φ : A →ₐ[K] B)
    (S : (saturated K Q).presentation.atlas.Index) (T : (saturated K P).presentation.atlas.Index)
    (h : (saturatedHom K P Q φ).baseMap '' Set.range ((saturated K Q).presentation.atlas.chart S) ⊆
      Set.range ((saturated K P).presentation.atlas.chart T)) (a : A) :
    (saturatedHom K P Q φ).pullback S T h
        (localAlgebraMap P ((presentation K P).atlas.saturatedRepresentative T) a) =
      localAlgebraMap Q ((presentation K Q).atlas.saturatedRepresentative S) (φ a) := by
  have h' : (strongHom K P Q φ).baseMap ''
      ((presentation K Q).atlas.saturatedRepresentative S).locus ⊆
      ((presentation K P).atlas.saturatedRepresentative T).locus := by
    rw [← LocalDomain.range_ambientMap, ← LocalDomain.range_ambientMap]
    exact h
  exact localDomainPullback_localAlgebraMap P Q φ _ _ h' a

end Langlands.Analytic.AffineAnalytification.LocalDomainMaps
