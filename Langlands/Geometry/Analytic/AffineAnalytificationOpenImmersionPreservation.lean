import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidNaturality
import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidLocalized
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.AffineAnalytificationMonomorphismComparison
import Langlands.Geometry.Analytic.AffineAnalytificationUniverseReduction
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Open immersions of affine spectra give analytic open immersions -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

namespace OpenImmersionPreservation

open CategoryTheory Set SaturatedAtlasPresentation ChartFamilyComparison PresentedAffinoidAlgebra

section Points

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
private theorem apply_eq_of_heq {X : Type*} {R S : PresentedAffinoidAlgebra K} (h : R = S)
    (c : BanachSpectrum R → X) (d : BanachSpectrum S → X) (hcd : HEq c d)
    (t : BanachSpectrum R) :
    c t = d (BanachSpectrum.comap (algebraCast h.symm).toBoundedRingHom t) := by
  subst h
  cases hcd
  congr 1

variable {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- A saturated original chart point, read in the original polynomial chart. -/
theorem saturated_chart_original (j : (presentation K P).atlas.Index)
    (t : BanachSpectrum ((saturated K P).presentation.atlas.algebra (originalIndex P j))) :
    (saturated K P).presentation.atlas.chart (originalIndex P j) t =
      (presentation K P).atlas.chart j
        (BanachSpectrum.comap (algebraCast (originalAlgebra P j).symm).toBoundedRingHom t) :=
  apply_eq_of_heq (originalAlgebra P j) _ _
    ((presentation K P).atlas.saturatedAtlas_original_chart_heq j) t

private theorem pointSeminorm_presentation_chart (j : (presentation K P).atlas.Index)
    (t : BanachSpectrum ((presentation K P).atlas.algebra j)) (a : A) :
    pointSeminorm K P ((presentation K P).atlas.chart j t) a = t (coordinateMap P j a) :=
  rfl

omit [CompleteSpace K] in
private theorem comap_apply' {R S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S)
    (t : BanachSpectrum S) (r : R) :
    BanachSpectrum.comap g.toBoundedRingHom t r = t (g r) :=
  rfl

omit [CompleteSpace K] in
private theorem boundedAlgHom_comp_toAlgHom {R S T : PresentedAffinoidAlgebra K}
    (g : BoundedAlgHom K S T) (h : BoundedAlgHom K R S) :
    (g.comp h).toAlgHom = g.toAlgHom.comp h.toAlgHom :=
  rfl

private theorem toAlgebraFamily_map_eq {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index) :
    (toAlgebraFamily P F).map i =
      chartAlgHom P F i (selectedTarget P F i) (selectedTarget_spec P F i) :=
  rfl

private theorem chartAlgHom_eq {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    chartAlgHom P F i j h = (originalPullback P F i j h).toAlgHom.comp (coordinateMap P j) :=
  rfl

private theorem originalPullback_eq {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    originalPullback P F i j h =
      (F.pullback i (originalIndex P j) (original_admissible P F i j h)).comp
        (algebraCast (originalAlgebra P j).symm) :=
  rfl

/-- The coordinate-algebra map on a source chart read through an admissible original
target chart of a strong map into an affine analytification. -/
def chartPullbackAlgHom {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    A →ₐ[K] S.presentation.atlas.algebra i :=
  (F.pullback i (originalIndex P j) (original_admissible P F i j h)).toAlgHom.comp
    ((algebraCast (originalAlgebra P j).symm).toAlgHom.comp (coordinateMap P j))

omit [CompleteSpace K] in
private theorem comp_comp_apply {R T U : PresentedAffinoidAlgebra K} (ρ : BoundedAlgHom K U T)
    (κ : BoundedAlgHom K R U) (c : A →ₐ[K] R) (a : A) :
    (ρ.toAlgHom.comp (κ.toAlgHom.comp c)) a = ρ (κ (c a)) :=
  rfl

private theorem chartPullbackAlgHom_eq {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    chartPullbackAlgHom P F i j h =
      (F.pullback i (originalIndex P j) (original_admissible P F i j h)).toAlgHom.comp
        ((algebraCast (originalAlgebra P j).symm).toAlgHom.comp (coordinateMap P j)) :=
  rfl

/-- The chart algebra map evaluated at an element. -/
theorem chartPullbackAlgHom_apply {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) (a : A) :
    chartPullbackAlgHom P F i j h a =
      (F.pullback i (originalIndex P j) (original_admissible P F i j h))
        ((algebraCast (originalAlgebra P j).symm) (coordinateMap P j a)) :=
  (congrArg (fun φ : A →ₐ[K] _ => φ a) (chartPullbackAlgHom_eq P F i j h)).trans
    (comp_comp_apply _ _ _ a)

private theorem pointSeminorm_baseMap_chart_aux {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (s : BanachSpectrum (S.presentation.atlas.algebra i)) (a : A) :
    pointSeminorm K P (F.baseMap (S.presentation.atlas.chart i s)) a =
      s ((F.pullback i (originalIndex P j) (original_admissible P F i j h))
        ((algebraCast (originalAlgebra P j).symm) (coordinateMap P j a))) := by
  rw [← F.chart_comm i (originalIndex P j) (original_admissible P F i j h) s,
    saturated_chart_original, pointSeminorm_presentation_chart, comap_apply', comap_apply']

/-- The seminorm of the image of a chart point under a strong map into an affine
analytification is computed by the chart algebra map read from the strong map. -/
theorem pointSeminorm_baseMap_chart {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (s : BanachSpectrum (S.presentation.atlas.algebra i)) (a : A) :
    pointSeminorm K P (F.baseMap (S.presentation.atlas.chart i s)) a =
      s (chartPullbackAlgHom P F i j h a) :=
  (pointSeminorm_baseMap_chart_aux P F i j h s a).trans
    (congrArg (fun r => s r) (chartPullbackAlgHom_apply P F i j h a).symm)

/-- The chart algebra map of the compatible algebra family of a strong map. -/
theorem toAlgebraFamily_map_eq_chartPullbackAlgHom {S : SaturatedAtlasPresentation.{u, u, u} K}
    (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    (toAlgebraFamily P F).map i = chartPullbackAlgHom P F i j h := by
  rw [toAlgebraFamily_map_eq, chartAlgHom_independent P F i _ j _ h, chartAlgHom_eq,
    originalPullback_eq, boundedAlgHom_comp_toAlgHom, chartPullbackAlgHom, AlgHom.comp_assoc]

end Points

section Lift

open _root_.AlgebraicGeometry

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (f : A →ₐ[K] B)

/-- An algebra map from `A` to an affinoid algebra factors through an open immersion
`Spec B → Spec A` when the centers of all points of the affinoid spectrum lie in its
image. -/
theorem exists_lift_of_center_mem
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (R : PresentedAffinoidAlgebra K) (φ : A →ₐ[K] R)
    (h : ∀ t, center K P ((saturatedAffinoidHom K P R φ).baseMap t) ∈
      (Set.range (Spec.map (CommRingCat.ofHom f.toRingHom)) : Set (PrimeSpectrum A))) :
    ∃ ψ : B →ₐ[K] R, ψ.comp f = φ := by
  let S₀ := SmallAffinoidSpectrum.saturated.{u, u} R
  let F₀ := saturatedAffinoidHom K P R φ
  let top := SmallAffinoidSpectrum.topIndex.{u, u} R
  let j := selectedTarget P F₀ top
  have hj := selectedTarget_spec P F₀ top
  let R' := S₀.presentation.atlas.algebra top
  let φ' : A →ₐ[K] R' := chartPullbackAlgHom P F₀ top j hj
  have hpt := pointSeminorm_baseMap_chart P F₀ top j hj
  have hφ' : (algebraCast (SmallAffinoidSpectrum.top_algebra R)).toAlgHom.comp φ' = φ := by
    have e := affinoidStrongAlgHom_saturatedAffinoidHom K P R φ
    unfold affinoidStrongAlgHom at e
    rw [toAlgebraFamily_map_eq_chartPullbackAlgHom P F₀ top j hj] at e
    exact e
  let W : Set (PrimeSpectrum A) := Set.range (Spec.map (CommRingCat.ofHom f.toRingHom))
  have hW : IsOpen W := IsOpenImmersion.isOpen_range _
  let G : Set A := {g | (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆ W}
  let I : Ideal R' := Ideal.span (φ' '' G)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨s, hs⟩ := exists_spectrum_kernel_of_proper_ideal R' I hne
    let x := F₀.baseMap (S₀.presentation.atlas.chart top s)
    have hx : center K P x ∈ W := h _
    obtain ⟨_, ⟨g, rfl⟩, hxg, hgW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hW
    have hne0 := (center_mem_basicOpen K P x g).mp hxg
    rw [hpt] at hne0
    exact hne0 (hs (Ideal.subset_span ⟨g, hgW, rfl⟩))
  have hrange : Set.range (Spec.map (CommRingCat.ofHom φ'.toRingHom)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    rintro _ ⟨𝔭, rfl⟩
    have hnot : ¬ I ≤ 𝔭.asIdeal := fun hle => 𝔭.isPrime.ne_top (top_unique (hI ▸ hle))
    rw [Ideal.span_le] at hnot
    obtain ⟨_, ⟨g, hg, rfl⟩, hgp⟩ := Set.not_subset.mp hnot
    exact hg (show PrimeSpectrum.comap φ'.toRingHom 𝔭 ∈ PrimeSpectrum.basicOpen g from hgp)
  let l := IsOpenImmersion.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom φ'.toRingHom)) hrange
  have hl := IsOpenImmersion.lift_fac (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom φ'.toRingHom)) hrange
  let ψ₀ : CommRingCat.of B ⟶ CommRingCat.of R' := Spec.preimage l
  have hψ₀ : CommRingCat.ofHom f.toRingHom ≫ ψ₀ = CommRingCat.ofHom φ'.toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, hl])
  have happ (a : A) : ψ₀.hom (f a) = φ' a :=
    congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of R' => g.hom a) hψ₀
  let ψ' : B →ₐ[K] R' :=
    { toRingHom := ψ₀.hom
      commutes' := fun k => by
        change ψ₀.hom (algebraMap K B k) = algebraMap K R' k
        rw [← f.commutes k, happ]
        exact φ'.commutes k }
  have hψ' : ψ'.comp f = φ' := AlgHom.ext fun a => happ a
  refine ⟨(algebraCast (SmallAffinoidSpectrum.top_algebra R)).toAlgHom.comp ψ', ?_⟩
  rw [AlgHom.comp_assoc, hψ', hφ']

end Lift

end OpenImmersionPreservation

open OpenImmersionPreservation CategoryTheory Set SaturatedAtlasPresentation _root_.AlgebraicGeometry

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option backward.isDefEq.respectTransparency false in
/-- An open immersion of affine spectra, with algebras in the universe of the field,
induces an analytic open immersion of affine analytifications. -/
theorem openImmersion_localizedHom_of_isOpenImmersion_of_univ {A B : Type u} [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))) :
    openImmersion (localizedHom K P Q f) := by
  have hepi : Epi (CommRingCat.ofHom f.toRingHom) :=
    ((UniverseReduction.isOpenImmersion_specMap_iff _).mp hf).2
  have : Mono (localizedHom K P Q f) := mono_localizedHom_of_epi P Q f
  let Y := localized K P
  let F := localizedHom K P Q f
  let W : Set (PrimeSpectrum A) := Set.range (Spec.map (CommRingCat.ofHom f.toRingHom))
  have hW : IsOpen W := IsOpenImmersion.isOpen_range _
  let U : Set (presentationOf Y).presentation.space := center K P ⁻¹' W
  have hU : IsOpen U := (continuous_center K P).isOpen_preimage W hW
  let D := (presentationOf Y).openDomain U hU
  have hFD : ∀ z, localizedSpaceFunctor.map F z ∈ D.carrier := by
    intro z
    change center K P ((localizedSpaceFunctor.map (localizedHom K P Q f)) z) ∈ W
    rw [localizedSpaceFunctor_map_localizedHom]
    change center K P (baseMap K P Q f z) ∈ W
    rw [center_baseMap]
    exact ⟨center K Q z, rfl⟩
  let F' := domainLift D F hFD
  let A₀ := (presentationOf Y).domain D
  have hRefines : AtlasTopology.LocallyRefines
      (range fun k : A₀.presentation.atlas.Index => range (A₀.presentation.atlas.chart k))
      {univ} := by
    intro V hV x _
    obtain rfl := mem_singleton_iff.mp hV
    obtain ⟨τ, hτ, hsub, hx, hn⟩ := A₀.presentation.atlas.isNet_chartFamily.1 x
    exact ⟨τ, hτ, hsub, fun S hS => ⟨subset_univ _, hx S hS⟩,
      by simpa only [nhdsWithin_univ] using hn⟩
  have hlocal : ∀ k : A₀.presentation.atlas.Index,
      ∃ l : localizationFunctor.obj (A₀.smallChartSpectrum k) ⟶ localized K Q,
        l ≫ F = localizationFunctor.map (A₀.smallChartSpectrumInclusion k) ≫ domainι Y D ∧
        l ≫ F = localizationFunctor.map (A₀.smallChartSpectrumInclusion k) ≫ domainι Y D := by
    intro k
    let R := A₀.presentation.atlas.algebra k
    let c : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, u} R) ⟶ localized K P :=
      localizationFunctor.map (A₀.smallChartSpectrumInclusion k) ≫ domainι Y D
    obtain ⟨φ, hφ⟩ := (localizedAffinoidHomEquiv K P R).surjective c
    rw [localizedAffinoidHomEquiv_apply] at hφ
    have hpts : ∀ t, center K P ((saturatedAffinoidHom K P R φ).baseMap t) ∈ W := by
      intro t
      have hmem : localizedSpaceFunctor.map c t ∈ D.carrier := by
        change localizedSpaceFunctor.map (localizationFunctor.map
          (A₀.smallChartSpectrumInclusion k) ≫ domainι Y D) t ∈ D.carrier
        rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
        exact (localizedSpaceFunctor.map (localizationFunctor.map
          (A₀.smallChartSpectrumInclusion k)) t).property
      rw [← hφ] at hmem
      change localizedSpaceFunctor.map (localizationFunctor.map
        (saturatedAffinoidHom K P R φ)) t ∈ D.carrier at hmem
      rw [localizedSpaceFunctor_map] at hmem
      exact hmem
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
    obtain ⟨ψ, hψ⟩ := exists_lift_of_center_mem P f R φ hpts
    have hl : localizedAffinoidHom K Q R ψ ≫ F = c := by
      change localizedAffinoidHom K Q R ψ ≫ localizedHom K P Q f = c
      rw [localizedAffinoidHom_comp, hψ, hφ]
    exact ⟨localizedAffinoidHom K Q R ψ, hl, hl⟩
  obtain ⟨G, hG, -⟩ := exists_lift_of_chartCover (A := A₀) (fun k => k) hRefines F F
    (fun _ a b h _ => (cancel_mono F).mp h) (domainι Y D) (domainι Y D) hlocal
  let e : localized K Q ≅ domainObj Y D :=
    { hom := F'
      inv := G
      hom_inv_id := (cancel_mono F).mp (by
        rw [Category.assoc, hG, domainLift_comp, Category.id_comp])
      inv_hom_id := (cancel_mono (domainι Y D)).mp (by
        rw [Category.assoc, domainLift_comp, hG, Category.id_comp]) }
  exact ⟨U, hU, e, domainLift_comp D F hFD⟩

/-- An open immersion of affine spectra induces an analytic open immersion of affine
analytifications. -/
theorem openImmersion_localizedHom_of_isOpenImmersion {A B : Type v} [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))) :
    openImmersion (localizedHom K P Q f) :=
  (UniverseReduction.openImmersion_iff_model P Q f).mpr
    (openImmersion_localizedHom_of_isOpenImmersion_of_univ _ _ _
      ((UniverseReduction.isOpenImmersion_iff_model P Q f).mp hf))

end Langlands.Analytic.AffineAnalytification
