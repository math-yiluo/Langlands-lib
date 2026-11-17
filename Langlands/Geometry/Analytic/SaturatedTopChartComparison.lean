import Langlands.Geometry.Analytic.TopChartAffinoidComparison
import Langlands.Geometry.Analytic.SmallAffinoidPullbacks

/-! # Greatest-chart comparison in the actual saturated category -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set PresentedAffinoidAlgebra
open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- Regard an actual saturated presentation with a greatest chart as a
greatest-chart presentation, retaining its entire atlas. -/
def asTopChart (A : SaturatedAtlasPresentation.{u, v, w} K)
    (t : A.presentation.atlas.Index)
    (ht : ∀ i, Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart t)) : TopChartPresentation.{u, v, w} K :=
  ⟨A.presentation, t, ht⟩

section Maps

variable (tA : A.presentation.atlas.Index) (tB : B.presentation.atlas.Index)
  (hA : ∀ i, Set.range (A.presentation.atlas.chart i) ⊆
    Set.range (A.presentation.atlas.chart tA))
  (hB : ∀ i, Set.range (B.presentation.atlas.chart i) ⊆
    Set.range (B.presentation.atlas.chart tB))

/-- A bounded map between the actual greatest-chart algebras constructs every
admissible pullback of a complete strong map. -/
def ofTopAlgebraMap
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra tB)
      (A.presentation.atlas.algebra tA)) : A ⟶ B :=
  TopChartPresentation.ofTopPullback
    (A := asTopChart A tA hA) (B := asTopChart B tB hB) φ

@[simp]
theorem pullbackAtTop_ofTopAlgebraMap
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra tB)
      (A.presentation.atlas.algebra tA)) :
    (ofTopAlgebraMap tA tB hA hB φ).pullbackAtTop tB hB tA = φ :=
  TopChartPresentation.topPullback_ofTopPullback
    (A := asTopChart A tA hA) (B := asTopChart B tB hB) φ

include hA in
/-- Equality of the actual top-algebra maps detects equality of the entire
strong maps in the saturated category. -/
theorem hom_ext_topAlgebra {f g : A ⟶ B}
    (h : f.pullbackAtTop tB hB tA = g.pullbackAtTop tB hB tA) : f = g :=
  TopChartPresentation.topPullback_injective
    (A := asTopChart A tA hA) (B := asTopChart B tB hB) h

@[simp]
theorem ofTopAlgebraMap_pullbackAtTop (f : A ⟶ B) :
    ofTopAlgebraMap tA tB hA hB (f.pullbackAtTop tB hB tA) = f := by
  apply hom_ext_topAlgebra tA tB hA hB
  exact pullbackAtTop_ofTopAlgebraMap tA tB hA hB _

/-- The full strong Hom type is in bijection with the actual bounded maps
between greatest-chart algebras. -/
def topAlgebraMapEquiv :
    (A ⟶ B) ≃ BoundedAlgHom K (B.presentation.atlas.algebra tB)
      (A.presentation.atlas.algebra tA) :=
  TopChartPresentation.topPullbackEquiv (asTopChart A tA hA) (asTopChart B tB hB)

end Maps

@[simp]
theorem id_pullbackAtTop (t : A.presentation.atlas.Index)
    (ht : ∀ i, Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart t)) :
    (𝟙 A : A ⟶ A).pullbackAtTop t ht t = BoundedAlgHom.id K _ :=
  A.presentation.atlas.restriction_id t _

/-- Equality of greatest-chart algebras gives an isomorphism of complete
strong maps in the actual saturated category. -/
def topChartIsoOfAlgebraEq
    (tA : A.presentation.atlas.Index) (tB : B.presentation.atlas.Index)
    (hA : ∀ i, Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart tA))
    (hB : ∀ i, Set.range (B.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart tB))
    (h : A.presentation.atlas.algebra tA = B.presentation.atlas.algebra tB) :
    A ≅ B where
  hom := ofTopAlgebraMap tA tB hA hB (eqToHom h.symm)
  inv := ofTopAlgebraMap tB tA hB hA (eqToHom h)
  hom_inv_id := by
    apply hom_ext_topAlgebra tA tA hA hA
    rw [pullbackAtTop_comp _ _ tB tA hB hA,
      pullbackAtTop_ofTopAlgebraMap, pullbackAtTop_ofTopAlgebraMap,
      id_pullbackAtTop]
    change (eqToHom h ≫ eqToHom h.symm) = 𝟙 _
    simp
  inv_hom_id := by
    apply hom_ext_topAlgebra tB tB hB hB
    rw [pullbackAtTop_comp _ _ tA tB hA hB,
      pullbackAtTop_ofTopAlgebraMap, pullbackAtTop_ofTopAlgebraMap,
      id_pullbackAtTop]
    change (eqToHom h.symm ≫ eqToHom h) = 𝟙 _
    simp

/-- Every actual chart spectrum is small in the ambient space universe. -/
theorem chartSpectrum_small (A : SaturatedAtlasPresentation.{u, v, w} K)
    (t : A.presentation.atlas.Index) :
    Small.{v} (BanachSpectrum (A.presentation.atlas.algebra t)) :=
  small_of_injective (f := A.presentation.atlas.chart t)
    (A.presentation.atlas.isEmbedding_chart t).injective

omit [CompleteSpace K] in
private theorem transported_map_comm
    {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R' = R) (hS : S' = S)
    (φ : BoundedAlgHom K S R) (φ' : BoundedAlgHom K S' R')
    (hφ : HEq φ' φ) :
    φ'.comp (eqToHom hS.symm) = (eqToHom hR.symm).comp φ := by
  cases hR
  cases hS
  cases eq_of_heq hφ
  rfl

section SmallComparison

attribute [local instance] chartSpectrum_small

variable {A₀ B₀ C₀ : SaturatedAtlasPresentation.{u, v, v} K}
  (tA : A₀.presentation.atlas.Index) (tB : B₀.presentation.atlas.Index)
  (hA : ∀ i, Set.range (A₀.presentation.atlas.chart i) ⊆
    Set.range (A₀.presentation.atlas.chart tA))
  (hB : ∀ i, Set.range (B₀.presentation.atlas.chart i) ⊆
    Set.range (B₀.presentation.atlas.chart tB))

/-- The small actual spectrum of the greatest-chart algebra is isomorphic
to the original saturated atlas by complete strong maps. -/
def smallSpectrumIso :
    SmallAffinoidSpectrum.saturated (A₀.presentation.atlas.algebra tA) ≅ A₀ :=
  topChartIsoOfAlgebraEq
    (SmallAffinoidSpectrum.topIndex _) tA
    (SmallAffinoidSpectrum.top_contains _) hA
    (SmallAffinoidSpectrum.top_algebra _)

/-- The comparison retains the greatest-chart algebra map, with its sole
transport along the retained original-chart equality. -/
theorem smallSpectrumIso_hom_pullbackAtTop :
    (smallSpectrumIso tA hA).hom.pullbackAtTop tA hA
      (SmallAffinoidSpectrum.topIndex _) =
        eqToHom (SmallAffinoidSpectrum.top_algebra
          (A₀.presentation.atlas.algebra tA)).symm :=
  pullbackAtTop_ofTopAlgebraMap _ _ _ _ _

/-- Complete strong maps are natural under comparison with the small actual
spectra of their greatest-chart algebras. -/
theorem smallSpectrumIso_naturality (f : A₀ ⟶ B₀) :
    SmallAffinoidSpectrum.map (f.pullbackAtTop tB hB tA) ≫
        (smallSpectrumIso tB hB).hom =
      (smallSpectrumIso tA hA).hom ≫ f := by
  apply hom_ext_topAlgebra (SmallAffinoidSpectrum.topIndex _) tB
    (SmallAffinoidSpectrum.top_contains _) hB
  rw [pullbackAtTop_comp _ _ (SmallAffinoidSpectrum.topIndex _) tB
      (SmallAffinoidSpectrum.top_contains _) hB,
    pullbackAtTop_comp _ _ tA tB hA hB,
    smallSpectrumIso_hom_pullbackAtTop, smallSpectrumIso_hom_pullbackAtTop]
  exact transported_map_comm
    (SmallAffinoidSpectrum.top_algebra _) (SmallAffinoidSpectrum.top_algebra _)
    _ _ (SmallAffinoidSpectrum.map_pullbackAtTop_heq _)

end SmallComparison

/-- A strict strong pullback gives refined strong universality using the
identity source refinement. -/
theorem refinedStrongPullback_of_strongIsPullback
    {P : SaturatedAtlasPresentation.{u, v, w} K}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback p q f g) :
    IsRefinedStrongPullback p q f g := by
  refine ⟨h.w, ?_, ?_⟩
  · intro T a b hab
    refine ⟨T, 𝟙 T, StrongHom.isQuasiIso_id T.presentation,
      h.lift a b hab, ?_, ?_⟩
    · simpa only [Category.id_comp] using h.lift_fst a b hab
    · simpa only [Category.id_comp] using h.lift_snd a b hab
  · intro T a b hp hq
    exact h.hom_ext hp hq

section GreatestChartPullback

attribute [local instance] chartSpectrum_small

variable {A₀ B₀ C₀ : SaturatedAtlasPresentation.{u, v, v} K}
  (f : A₀ ⟶ C₀) (g : B₀ ⟶ C₀)
  (tA : A₀.presentation.atlas.Index) (tB : B₀.presentation.atlas.Index)
  (tC : C₀.presentation.atlas.Index)
  (hA : ∀ i, Set.range (A₀.presentation.atlas.chart i) ⊆
    Set.range (A₀.presentation.atlas.chart tA))
  (hB : ∀ i, Set.range (B₀.presentation.atlas.chart i) ⊆
    Set.range (B₀.presentation.atlas.chart tB))
  (hC : ∀ i, Set.range (C₀.presentation.atlas.chart i) ⊆
    Set.range (C₀.presentation.atlas.chart tC))

section SmallPushout

variable [Small.{v} (BanachSpectrum (AffinoidPushout.algebra
  (f.pullbackAtTop tC hC tA) (g.pullbackAtTop tC hC tB)))]

/-- The small actual closed-quotient pushout of the greatest-chart algebras. -/
def greatestChartPullback : SaturatedAtlasPresentation.{u, v, v} K :=
  SmallAffinoidSpectrum.pushout (f.pullbackAtTop tC hC tA) (g.pullbackAtTop tC hC tB)

/-- The first projection retains the original saturated target atlas. -/
def greatestChartPullbackFst : greatestChartPullback f g tA tB tC hC ⟶ A₀ :=
  SmallAffinoidSpectrum.pushoutFst (f.pullbackAtTop tC hC tA)
    (g.pullbackAtTop tC hC tB) ≫ (smallSpectrumIso tA hA).hom

/-- The second projection retains the original saturated target atlas. -/
def greatestChartPullbackSnd : greatestChartPullback f g tA tB tC hC ⟶ B₀ :=
  SmallAffinoidSpectrum.pushoutSnd (f.pullbackAtTop tC hC tA)
    (g.pullbackAtTop tC hC tB) ≫ (smallSpectrumIso tB hB).hom

/-- Arbitrary saturated presentations with greatest charts have the full
strong pullback whenever their actual algebraic pushout spectrum is small. -/
theorem greatestChartPullback_isPullback :
    IsPullback (greatestChartPullbackFst f g tA tB tC hA hC)
      (greatestChartPullbackSnd f g tA tB tC hB hC) f g := by
  apply (SmallAffinoidSpectrum.pushout_isPullback
    (f.pullbackAtTop tC hC tA) (g.pullbackAtTop tC hC tB)).of_iso
    (Iso.refl _) (smallSpectrumIso tA hA) (smallSpectrumIso tB hB)
    (smallSpectrumIso tC hC)
  · exact (Category.id_comp (greatestChartPullbackFst f g tA tB tC hA hC)).symm
  · exact (Category.id_comp (greatestChartPullbackSnd f g tA tB tC hB hC)).symm
  · exact smallSpectrumIso_naturality tA tC hA hC f
  · exact smallSpectrumIso_naturality tB tC hB hC g

/-- The same square has refined strong universality. -/
theorem greatestChartPullback_isRefinedStrongPullback :
    IsRefinedStrongPullback (greatestChartPullbackFst f g tA tB tC hA hC)
      (greatestChartPullbackSnd f g tA tB tC hB hC) f g :=
  refinedStrongPullback_of_strongIsPullback
    (greatestChartPullback_isPullback f g tA tB tC hA hB hC)

/-- These projections are universal against all localized test morphisms. -/
theorem greatestChartPullback_localized_isPullback :
    IsPullback
      (localizationFunctor.map (greatestChartPullbackFst f g tA tB tC hA hC))
      (localizationFunctor.map (greatestChartPullbackSnd f g tA tB tC hB hC))
      (localizationFunctor.map f) (localizationFunctor.map g) :=
  (greatestChartPullback_isRefinedStrongPullback f g tA tB tC hA hB hC).isPullback

end SmallPushout

include tB hA hB in
/-- Finite Banach base change supplies a pullback of the original saturated
greatest-chart presentations in the independent space universe. -/
theorem exists_greatestChart_finite_isPullback
    (h : AffinoidPushout.FiniteBanachPushoutStatement K)
    (hf : (f.pullbackAtTop tC hC tA).IsFiniteBanach) :
    ∃ (P : SaturatedAtlasPresentation.{u, v, v} K) (p : P ⟶ A₀) (q : P ⟶ B₀),
      IsPullback p q f g ∧ IsRefinedStrongPullback p q f g := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout
    (f.pullbackAtTop tC hC tA) (g.pullbackAtTop tC hC tB) h hf
  exact ⟨greatestChartPullback f g tA tB tC hC,
    greatestChartPullbackFst f g tA tB tC hA hC,
    greatestChartPullbackSnd f g tA tB tC hB hC,
    greatestChartPullback_isPullback f g tA tB tC hA hB hC,
    greatestChartPullback_isRefinedStrongPullback f g tA tB tC hA hB hC⟩

include tB hA hB in
/-- The finite Banach construction also supplies the full localized pullback
while retaining the original objects and complete morphisms of the cospan. -/
theorem exists_greatestChart_finite_localized_isPullback
    (h : AffinoidPushout.FiniteBanachPushoutStatement K)
    (hf : (f.pullbackAtTop tC hC tA).IsFiniteBanach) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K))
      (p : P ⟶ localizationFunctor.obj A₀) (q : P ⟶ localizationFunctor.obj B₀),
      IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g) := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout
    (f.pullbackAtTop tC hC tA) (g.pullbackAtTop tC hC tB) h hf
  exact ⟨localizationFunctor.obj (greatestChartPullback f g tA tB tC hC),
    localizationFunctor.map (greatestChartPullbackFst f g tA tB tC hA hC),
    localizationFunctor.map (greatestChartPullbackSnd f g tA tB tC hB hC),
    greatestChartPullback_localized_isPullback f g tA tB tC hA hB hC⟩

end GreatestChartPullback

end Langlands.Analytic.SaturatedAtlasPresentation
