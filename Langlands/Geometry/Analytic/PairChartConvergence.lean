import Langlands.Geometry.Analytic.PairChartPatch
import Langlands.Geometry.Analytic.AffinoidPatchPullback
import Langlands.Geometry.Analytic.PullbackActionTests
import Langlands.Geometry.Analytic.AffinoidPushoutSpectralTests

/-! # Spectral convergence of a pullback action on pair charts -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set Filter Topology PresentedAffinoidAlgebra
open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A bounded map transported along equalities of its source and target. -/
theorem boundedAlgHom_transport_comm {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R' = R) (hS : S' = S)
    (φ : BoundedAlgHom K S R) (φ' : BoundedAlgHom K S' R')
    (hφ : HEq φ' φ) :
    φ'.comp (eqToHom hS.symm) = (eqToHom hR.symm).comp φ := by
  cases hR
  cases hS
  cases eq_of_heq hφ
  rfl

omit [CompleteSpace K] in
/-- Spectral convergence of endomorphisms is detected after transport of the
algebra along an equality. -/
theorem spectralConvergesOn_of_transport {T : Type z} {l : Filter T}
    {A' A : PresentedAffinoidAlgebra K} (h : A' = A) {Φ : T → BoundedAlgHom K A' A'}
    (H : ∀ b : A, SpectralConvergesOn l (fun t => (Φ t).comp (eqToHom h.symm))
      (eqToHom h.symm) b) (a : A') :
    SpectralConvergesOn l Φ (BoundedAlgHom.id K A') a := by
  subst h
  exact H a

theorem localizationFunctor_map_localizedTopTargetHomEquiv_symm
    {A B : SaturatedAtlasPresentation.{u, v, v} K} (j : B.presentation.atlas.Index)
    (hj : ∀ i, range (B.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j))
    (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    localizationFunctor.map ((localizedTopTargetHomEquiv j hj).symm φ) = φ := by
  rw [← localizedTopTargetHomEquiv_apply j hj, Equiv.apply_symm_apply]

attribute [local instance] chartSpectrum_small

namespace PairChartData

variable {B U V P : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ B} {g : V ⟶ B}
  (c : PairChartData f g)

section Top

variable [hc : Small.{v} (BanachSpectrum c.algebra)]
include hc

/-- The greatest chart of the pair chart: the whole spectrum of the pushout algebra. -/
def top : c.obj.presentation.atlas.Index := SmallAffinoidSpectrum.topIndex c.algebra

theorem top_contains (i : c.obj.presentation.atlas.Index) :
    range (c.obj.presentation.atlas.chart i) ⊆ range (c.obj.presentation.atlas.chart c.top) :=
  SmallAffinoidSpectrum.top_contains c.algebra i

theorem top_algebra : c.obj.presentation.atlas.algebra c.top = c.algebra :=
  SmallAffinoidSpectrum.top_algebra c.algebra

/-- The complete strong first projection of the pair chart. -/
def strongFst : c.obj ⟶ (presentationOf U).domain c.leftDomain :=
  @greatestChartPullbackFst _ _ _ _ _ _ _
    (chartDomainStrong f c.left c.base c.left_mapsTo)
    (chartDomainStrong g c.right c.base c.right_mapsTo)
    (chartDomainFullChart _ c.left) (chartDomainFullChart _ c.right)
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.left)
    (range_chart_subset_chartDomainFullChart _ c.base) hc

/-- The complete strong second projection of the pair chart. -/
def strongSnd : c.obj ⟶ (presentationOf V).domain c.rightDomain :=
  @greatestChartPullbackSnd _ _ _ _ _ _ _
    (chartDomainStrong f c.left c.base c.left_mapsTo)
    (chartDomainStrong g c.right c.base c.right_mapsTo)
    (chartDomainFullChart _ c.left) (chartDomainFullChart _ c.right)
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.right)
    (range_chart_subset_chartDomainFullChart _ c.base) hc

theorem fst_eq : c.fst = localizationFunctor.map c.strongFst := rfl

theorem snd_eq : c.snd = localizationFunctor.map c.strongSnd := rfl

/-- The first projection on greatest charts. -/
def fstTop : BoundedAlgHom K ((presentationOf U).presentation.atlas.algebra c.left)
    (c.obj.presentation.atlas.algebra c.top) :=
  c.strongFst.pullbackAtTop (chartDomainFullChart _ c.left)
    (range_chart_subset_chartDomainFullChart _ c.left) c.top

/-- The second projection on greatest charts. -/
def sndTop : BoundedAlgHom K ((presentationOf V).presentation.atlas.algebra c.right)
    (c.obj.presentation.atlas.algebra c.top) :=
  c.strongSnd.pullbackAtTop (chartDomainFullChart _ c.right)
    (range_chart_subset_chartDomainFullChart _ c.right) c.top

/-- On greatest charts, the first projection is the left pushout map. -/
theorem fstTop_eq : c.fstTop =
    (eqToHom c.top_algebra.symm).comp (AffinoidPushout.leftMap c.leftTop c.rightTop) := by
  have h := pullbackAtTop_comp (SmallAffinoidSpectrum.pushoutFst c.leftTop c.rightTop)
    (smallSpectrumIso (chartDomainFullChart (presentationOf U) c.left)
      (range_chart_subset_chartDomainFullChart _ c.left)).hom
    (SmallAffinoidSpectrum.topIndex _) (chartDomainFullChart (presentationOf U) c.left)
    (SmallAffinoidSpectrum.top_contains _) (range_chart_subset_chartDomainFullChart _ c.left)
    c.top
  erw [smallSpectrumIso_hom_pullbackAtTop] at h
  refine (show c.fstTop = _ from h).trans ?_
  exact boundedAlgHom_transport_comm (SmallAffinoidSpectrum.top_algebra _)
    (SmallAffinoidSpectrum.top_algebra _) _ _
    (SmallAffinoidSpectrum.map_pullbackAtTop_heq (AffinoidPushout.leftMap _ _))

/-- On greatest charts, the second projection is the right pushout map. -/
theorem sndTop_eq : c.sndTop =
    (eqToHom c.top_algebra.symm).comp (AffinoidPushout.rightMap c.leftTop c.rightTop) := by
  have h := pullbackAtTop_comp (SmallAffinoidSpectrum.pushoutSnd c.leftTop c.rightTop)
    (smallSpectrumIso (chartDomainFullChart (presentationOf V) c.right)
      (range_chart_subset_chartDomainFullChart _ c.right)).hom
    (SmallAffinoidSpectrum.topIndex _) (chartDomainFullChart (presentationOf V) c.right)
    (SmallAffinoidSpectrum.top_contains _) (range_chart_subset_chartDomainFullChart _ c.right)
    c.top
  erw [smallSpectrumIso_hom_pullbackAtTop] at h
  refine (show c.sndTop = _ from h).trans ?_
  exact boundedAlgHom_transport_comm (SmallAffinoidSpectrum.top_algebra _)
    (SmallAffinoidSpectrum.top_algebra _) _ _
    (SmallAffinoidSpectrum.map_pullbackAtTop_heq (AffinoidPushout.rightMap _ _))

end Top

section Eventually

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- A continuous action eventually preserves a given chart domain. -/
theorem _root_.Langlands.Analytic.SaturatedAtlasPresentation.IsContinuousAction.eventually_preimage_chartDomain
    {X : LocalizedCategory.{u, v, v} (K := K)} {σX : G →* Aut X} (hX : IsContinuousAction σX)
    (i : (presentationOf X).presentation.atlas.Index) :
    ∀ᶠ a in 𝓝 (1 : G), localizedSpaceFunctor.map (σX a).hom ⁻¹'
      ((presentationOf X).chartDomain i).carrier = ((presentationOf X).chartDomain i).carrier := by
  let τ : TestTriple (presentationOf X) := ⟨i, 0, 1, zero_lt_one⟩
  filter_upwards [hX τ] with a ha
  have hchart := (show IsNear τ (σX a).hom (𝟙 X) from ha).preimage_eq
  rw [CategoryTheory.Functor.map_id, TopCat.coe_id] at hchart
  change _ = τ.locus at hchart
  exact hchart

variable {σ : G →* Aut P} {σU : G →* Aut U} {σV : G →* Aut V} {p : P ⟶ U} {q : P ⟶ V}

/-- An action compatible with continuous actions on both factors eventually
preserves the patch of a pair chart. -/
theorem eventually_preimage_patch (hU : IsContinuousAction σU) (hV : IsContinuousAction σV)
    (hp : ∀ a, (σ a).hom ≫ p = p ≫ (σU a).hom) (hq : ∀ a, (σ a).hom ≫ q = q ≫ (σV a).hom) :
    ∀ᶠ a in 𝓝 (1 : G), localizedSpaceFunctor.map (σ a).hom ⁻¹' (c.patch p q).carrier =
      (c.patch p q).carrier :=
  eventually_preimage_eq_pullback_patch hU hV p q hp hq c.left c.right

end Eventually

variable {p : P ⟶ U} {q : P ⟶ V} (hP : IsPullback p q f g)
  [hc : Small.{v} (BanachSpectrum c.algebra)]
include hP hc

/-- An endomorphism of the pullback compatible with an endomorphism of the
first factor which preserves the left chart: conjugated to the pair chart, it
commutes with the first projection. -/
theorem patchConj_fst (φ : P ⟶ P) (φU : U ⟶ U) (hφ : φ ≫ p = p ≫ φU)
    (hE : ∀ x ∈ (c.patch p q).carrier, localizedSpaceFunctor.map φ x ∈ (c.patch p q).carrier)
    (hU : ∀ x ∈ c.leftDomain.carrier, localizedSpaceFunctor.map φU x ∈ c.leftDomain.carrier) :
    patchConj (c.patch p q) (c.patchIso hP) φ hE ≫ c.fst =
      c.fst ≫ domainRestrict _ _ φU hU := by
  apply (cancel_mono (domainι U c.leftDomain)).1
  unfold patchConj
  simp only [patchIso_hom, patchIso_inv, Category.assoc, fromPatch_fst_assoc, patchFst_comp,
    domainRestrict_comp_assoc, toPatch_comp_assoc, domainRestrict_comp, hφ]
  rw [← Category.assoc, toP_fst, Category.assoc]

/-- The symmetric statement for the second projection. -/
theorem patchConj_snd (φ : P ⟶ P) (φV : V ⟶ V) (hφ : φ ≫ q = q ≫ φV)
    (hE : ∀ x ∈ (c.patch p q).carrier, localizedSpaceFunctor.map φ x ∈ (c.patch p q).carrier)
    (hV : ∀ x ∈ c.rightDomain.carrier, localizedSpaceFunctor.map φV x ∈ c.rightDomain.carrier) :
    patchConj (c.patch p q) (c.patchIso hP) φ hE ≫ c.snd =
      c.snd ≫ domainRestrict _ _ φV hV := by
  apply (cancel_mono (domainι V c.rightDomain)).1
  unfold patchConj
  simp only [patchIso_hom, patchIso_inv, Category.assoc, fromPatch_snd_assoc, patchSnd_comp,
    domainRestrict_comp_assoc, toPatch_comp_assoc, domainRestrict_comp, hφ]
  rw [← Category.assoc, toP_snd, Category.assoc]

/-- The patch pullback intertwines the first projection on greatest charts
with the preserved-chart pullback of the first factor. -/
theorem patchPullback_comp_fstTop (φ : P ⟶ P) (φU : U ⟶ U) (hφ : φ ≫ p = p ≫ φU)
    (hE : localizedSpaceFunctor.map φ ⁻¹' (c.patch p q).carrier = (c.patch p q).carrier)
    (hU : localizedSpaceFunctor.map φU ⁻¹' c.leftDomain.carrier = c.leftDomain.carrier) :
    (patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) φ).comp c.fstTop =
      c.fstTop.comp (preservedChartPullback c.left φU) := by
  rw [patchPullback_of_preimage_eq _ _ _ _ _ hE, preservedChartPullback_of_preimage_eq _ _ hU]
  have hs : (localizedTopTargetHomEquiv c.top c.top_contains).symm
        (patchConj (c.patch p q) (c.patchIso hP) φ (mapsTo_of_preimage_eq _ hE)) ≫
          c.strongFst =
      c.strongFst ≫ (localizedTopTargetHomEquiv (chartDomainFullChart (presentationOf U) c.left)
        (range_chart_subset_chartDomainFullChart _ c.left)).symm
        (domainRestrict _ _ φU (mapsTo_chart_of_preimage_eq c.left φU hU)) := by
    apply localizationFunctor_map_injective
    simp only [Functor.map_comp, localizationFunctor_map_localizedTopTargetHomEquiv_symm]
    rw [← fst_eq]
    exact c.patchConj_fst hP φ φU hφ _ _
  have h1 := pullbackAtTop_comp ((localizedTopTargetHomEquiv c.top c.top_contains).symm
        (patchConj (c.patch p q) (c.patchIso hP) φ (mapsTo_of_preimage_eq _ hE)))
    c.strongFst c.top (chartDomainFullChart (presentationOf U) c.left) c.top_contains
    (range_chart_subset_chartDomainFullChart _ c.left) c.top
  have h2 := pullbackAtTop_comp c.strongFst
    ((localizedTopTargetHomEquiv (chartDomainFullChart (presentationOf U) c.left)
        (range_chart_subset_chartDomainFullChart _ c.left)).symm
        (domainRestrict _ _ φU (mapsTo_chart_of_preimage_eq c.left φU hU)))
    (chartDomainFullChart (presentationOf U) c.left) (chartDomainFullChart (presentationOf U) c.left)
    (range_chart_subset_chartDomainFullChart _ c.left) (range_chart_subset_chartDomainFullChart _ c.left)
    c.top
  rw [hs] at h1
  exact h1.symm.trans h2

/-- The patch pullback intertwines the second projection on greatest charts
with the preserved-chart pullback of the second factor. -/
theorem patchPullback_comp_sndTop (φ : P ⟶ P) (φV : V ⟶ V) (hφ : φ ≫ q = q ≫ φV)
    (hE : localizedSpaceFunctor.map φ ⁻¹' (c.patch p q).carrier = (c.patch p q).carrier)
    (hV : localizedSpaceFunctor.map φV ⁻¹' c.rightDomain.carrier = c.rightDomain.carrier) :
    (patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) φ).comp c.sndTop =
      c.sndTop.comp (preservedChartPullback c.right φV) := by
  rw [patchPullback_of_preimage_eq _ _ _ _ _ hE, preservedChartPullback_of_preimage_eq _ _ hV]
  have hs : (localizedTopTargetHomEquiv c.top c.top_contains).symm
        (patchConj (c.patch p q) (c.patchIso hP) φ (mapsTo_of_preimage_eq _ hE)) ≫
          c.strongSnd =
      c.strongSnd ≫ (localizedTopTargetHomEquiv (chartDomainFullChart (presentationOf V) c.right)
        (range_chart_subset_chartDomainFullChart _ c.right)).symm
        (domainRestrict _ _ φV (mapsTo_chart_of_preimage_eq c.right φV hV)) := by
    apply localizationFunctor_map_injective
    simp only [Functor.map_comp, localizationFunctor_map_localizedTopTargetHomEquiv_symm]
    rw [← snd_eq]
    exact c.patchConj_snd hP φ φV hφ _ _
  have h1 := pullbackAtTop_comp ((localizedTopTargetHomEquiv c.top c.top_contains).symm
        (patchConj (c.patch p q) (c.patchIso hP) φ (mapsTo_of_preimage_eq _ hE)))
    c.strongSnd c.top (chartDomainFullChart (presentationOf V) c.right) c.top_contains
    (range_chart_subset_chartDomainFullChart _ c.right) c.top
  have h2 := pullbackAtTop_comp c.strongSnd
    ((localizedTopTargetHomEquiv (chartDomainFullChart (presentationOf V) c.right)
        (range_chart_subset_chartDomainFullChart _ c.right)).symm
        (domainRestrict _ _ φV (mapsTo_chart_of_preimage_eq c.right φV hV)))
    (chartDomainFullChart (presentationOf V) c.right) (chartDomainFullChart (presentationOf V) c.right)
    (range_chart_subset_chartDomainFullChart _ c.right) (range_chart_subset_chartDomainFullChart _ c.right)
    c.top
  rw [hs] at h1
  exact h1.symm.trans h2

section Convergence

variable {G : Type z} [Group G] [TopologicalSpace G]
  {σ : G →* Aut P} {σU : G →* Aut U} {σV : G →* Aut V}

/-- The patch pullbacks of a compatible action converge spectrally to the
identity on the greatest-chart algebra of the pair chart. -/
theorem spectralConvergesOn_patchPullback (hU : IsContinuousAction σU)
    (hV : IsContinuousAction σV)
    (hp : ∀ a, (σ a).hom ≫ p = p ≫ (σU a).hom) (hq : ∀ a, (σ a).hom ≫ q = q ≫ (σV a).hom)
    (x : c.obj.presentation.atlas.algebra c.top) :
    SpectralConvergesOn (𝓝 (1 : G))
      (fun a => patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) (σ a).hom)
      (BoundedAlgHom.id K _) x := by
  apply spectralConvergesOn_of_transport c.top_algebra
  intro b
  apply AffinoidPushout.spectralConvergesOn_of_factors c.leftTop c.rightTop
  · intro y ε hε
    filter_upwards [c.eventually_preimage_patch hU hV hp hq,
      hU.eventually_preimage_chartDomain c.left,
      hU.spectralConvergesOn_preservedChartPullback c.left y ε hε] with a hE hL hy
    have key : patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) (σ a).hom
        (c.fstTop y) = c.fstTop (preservedChartPullback c.left (σU a).hom y) :=
      congrArg (fun F => F y) (c.patchPullback_comp_fstTop hP _ _ (hp a) hE hL)
    have hfy : c.fstTop y = ((eqToHom c.top_algebra.symm).comp
        (AffinoidPushout.leftMap c.leftTop c.rightTop)) y :=
      congrArg (fun F => F y) c.fstTop_eq
    have hb := hy.map c.fstTop.toBoundedRingHom
    rw [map_sub] at hb
    show BanachSpectrum.SpectralBound
      (patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) (σ a).hom
        (((eqToHom c.top_algebra.symm).comp (AffinoidPushout.leftMap c.leftTop c.rightTop)) y) -
        ((eqToHom c.top_algebra.symm).comp (AffinoidPushout.leftMap c.leftTop c.rightTop)) y) ε
    rw [← hfy, key]
    exact hb
  · intro y ε hε
    filter_upwards [c.eventually_preimage_patch hU hV hp hq,
      hV.eventually_preimage_chartDomain c.right,
      hV.spectralConvergesOn_preservedChartPullback c.right y ε hε] with a hE hR hy
    have key : patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) (σ a).hom
        (c.sndTop y) = c.sndTop (preservedChartPullback c.right (σV a).hom y) :=
      congrArg (fun F => F y) (c.patchPullback_comp_sndTop hP _ _ (hq a) hE hR)
    have hfy : c.sndTop y = ((eqToHom c.top_algebra.symm).comp
        (AffinoidPushout.rightMap c.leftTop c.rightTop)) y :=
      congrArg (fun F => F y) c.sndTop_eq
    have hb := hy.map c.sndTop.toBoundedRingHom
    rw [map_sub] at hb
    show BanachSpectrum.SpectralBound
      (patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) (σ a).hom
        (((eqToHom c.top_algebra.symm).comp (AffinoidPushout.rightMap c.leftTop c.rightTop)) y) -
        ((eqToHom c.top_algebra.symm).comp (AffinoidPushout.rightMap c.leftTop c.rightTop)) y) ε
    rw [← hfy, key]
    exact hb

end Convergence

end PairChartData

end Langlands.Analytic.SaturatedAtlasPresentation
