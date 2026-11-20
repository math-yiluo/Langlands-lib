import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover
import Langlands.Geometry.Analytic.FibreProductLocalizedLimit
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Proper maps on underlying spaces of analytic pullbacks -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

private theorem isCompact_preimage_snd [T2Space B.space] [T2Space C.space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hf : IsProperMap f.baseMap) {L : Set B.space} (hL : IsCompact L) :
    IsCompact (snd f g ⁻¹' L) := by
  classical
  have hInverse : IsCompact (f.baseMap ⁻¹' (g.baseMap '' L)) :=
    hf.isCompact_preimage (hL.image g.baseMap.continuous)
  obtain ⟨σ, hσfinite, hσcharts, hσcover⟩ :=
    A.atlas.isNet_chartFamily.1.exists_finite_cover_of_isCompact hInverse
  obtain ⟨τ, hτfinite, hτcharts, hτcover⟩ :=
    B.atlas.isNet_chartFamily.1.exists_finite_cover_of_isCompact hL
  let : Finite σ := hσfinite.to_subtype
  let : Finite τ := hτfinite.to_subtype
  let patches : Set (chartSystem f g).Space :=
    ⋃ V : σ, ⋃ W : τ, fst f g ⁻¹' V.val ∩ snd f g ⁻¹' W.val
  have hPatches : IsCompact patches := by
    refine isCompact_iUnion fun V => isCompact_iUnion fun W => ?_
    obtain ⟨a, ha⟩ := hσcharts V.property
    obtain ⟨b, hb⟩ := hτcharts W.property
    obtain ⟨Q, hQfinite, _, hQ⟩ := exists_finite_pairs f g hA hB a b
    rw [← ha, ← hb, hQ]
    exact hQfinite.isCompact_biUnion fun p _ =>
      isCompact_range ((chartSystem f g).continuous_chart p)
  refine hPatches.of_isClosed_subset (hL.isClosed.preimage (continuous_snd f g)) ?_
  intro z hz
  have hFirst : fst f g z ∈ f.baseMap ⁻¹' (g.baseMap '' L) :=
    ⟨snd f g z, hz, (baseMap_fst f g z).symm⟩
  obtain ⟨V, hV, hzV⟩ := hσcover hFirst
  obtain ⟨W, hW, hzW⟩ := hτcover hz
  exact mem_iUnion.mpr ⟨⟨V, hV⟩, mem_iUnion.mpr ⟨⟨W, hW⟩, hzV, hzW⟩⟩

end FibreProduct

namespace SaturatedAtlasPresentation

private theorem isProperMap_smallFibreProductSnd
    {A B C : SaturatedAtlasPresentation.{u, u, u} K} (f : A ⟶ C) (g : B ⟶ C)
    [T2Space B.presentation.space] [T2Space C.presentation.space]
    (hf : IsProperMap f.baseMap) :
    IsProperMap (smallFibreProductSnd f g).baseMap := by
  let F := geometricCompatibleMap f
  let G := geometricCompatibleMap g
  let : LocallyCompactSpace B.presentation.space := B.presentation.atlas.locallyCompactSpace
  have hProper : IsProperMap (FibreProduct.snd F G) :=
    isProperMap_iff_isCompact_preimage.mpr
      ⟨FibreProduct.continuous_snd F G,
        fun _ hL => FibreProduct.isCompact_preimage_snd F G A.hasAllLocalDomains
          B.hasAllLocalDomains hf hL⟩
  exact hProper.comp (FibreProduct.smallSpaceHomeomorph F G A.hasAllLocalDomains
    B.hasAllLocalDomains C.hasAllLocalDomains).symm.isProperMap

section RightFractions

variable {A B C : SaturatedAtlasPresentation.{u, u, u} K}
    (φ : (quasiIsomorphisms (K := K)).RightFraction A C)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C)
    {P : LocalizedCategory.{u, u, u} (K := K)}
    {p : P ⟶ localizationFunctor.obj A} {q : P ⟶ localizationFunctor.obj B}

private theorem rightFractionNumerator_isPullback
    (h : IsPullback p q (localizedRightFraction φ) (localizedRightFraction ψ)) :
    IsPullback (p ≫ (localizedQuasiIso φ.s φ.hs).inv)
      (q ≫ (localizedQuasiIso ψ.s ψ.hs).inv)
      (localizationFunctor.map φ.f) (localizationFunctor.map ψ.f) := by
  apply h.of_iso (Iso.refl _) (localizedQuasiIso φ.s φ.hs).symm
    (localizedQuasiIso ψ.s ψ.hs).symm (Iso.refl _)
  · simp
  · simp
  · simp [localizedRightFraction]
  · simp [localizedRightFraction]

/-- Compare a pullback of right fractions with the localized small fibre
product of their strong numerators. -/
def rightFractionNumeratorPullbackIso
    (h : IsPullback p q (localizedRightFraction φ) (localizedRightFraction ψ)) :
    P ≅ localizationFunctor.obj (smallFibreProduct φ.f ψ.f) :=
  (rightFractionNumerator_isPullback φ ψ h).isoIsPullback _ _
    (smallFibreProduct_isPullback φ.f ψ.f)

@[reassoc]
theorem rightFractionNumeratorPullbackIso_hom_snd
    (h : IsPullback p q (localizedRightFraction φ) (localizedRightFraction ψ)) :
    (rightFractionNumeratorPullbackIso φ ψ h).hom ≫
        localizationFunctor.map (smallFibreProductSnd φ.f ψ.f) =
      q ≫ (localizedQuasiIso ψ.s ψ.hs).inv :=
  (rightFractionNumerator_isPullback φ ψ h).isoIsPullback_hom_snd _ _
    (smallFibreProduct_isPullback φ.f ψ.f)

end RightFractions

/-- A topologically proper analytic map has topologically proper pullback projection
when the base and the target of the projection are Hausdorff. -/
theorem isProperMap_snd_of_isPullback
    {P A B C : LocalizedCategory.{u, u, u} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    [hBtop : T2Space (localizedSpaceFunctor.obj B)]
    [hCtop : T2Space (localizedSpaceFunctor.obj C)]
    (h : IsPullback p q f g) (hf : IsProperMap (localizedSpaceFunctor.map f)) :
    IsProperMap (localizedSpaceFunctor.map q) := by
  obtain ⟨A₀, hA⟩ := localizedObjectEquiv.surjective A
  obtain ⟨B₀, hB⟩ := localizedObjectEquiv.surjective B
  obtain ⟨C₀, hC⟩ := localizedObjectEquiv.surjective C
  change localizationFunctor.obj A₀ = A at hA
  change localizationFunctor.obj B₀ = B at hB
  change localizationFunctor.obj C₀ = C at hC
  subst A B C
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  let eA := localizedQuasiIso φ.s φ.hs
  let eB := localizedQuasiIso ψ.s ψ.hs
  let eBtop := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eB)
  let : T2Space ψ.X'.presentation.space :=
    haveI := hBtop
    eBtop.symm.t2Space
  let : T2Space C₀.presentation.space := hCtop
  have hφ : IsProperMap φ.f.baseMap := by
    change IsProperMap (localizedSpaceFunctor.map (localizationFunctor.map φ.f))
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ, Functor.map_comp,
      TopCat.coe_comp]
    exact hf.comp (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eA)).isProperMap
  let e := rightFractionNumeratorPullbackIso φ ψ h
  have hq : IsProperMap (localizedSpaceFunctor.map (q ≫ eB.inv)) := by
    change IsProperMap (localizedSpaceFunctor.map
      (q ≫ (localizedQuasiIso ψ.s ψ.hs).inv))
    rw [← rightFractionNumeratorPullbackIso_hom_snd φ ψ h, Functor.map_comp, TopCat.coe_comp]
    exact (isProperMap_smallFibreProductSnd φ.f ψ.f hφ).comp
      (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)).isProperMap
  have hComp : IsProperMap (localizedSpaceFunctor.map ((q ≫ eB.inv) ≫ eB.hom)) := by
    rw [Functor.map_comp, TopCat.coe_comp]
    exact eBtop.isProperMap.comp hq
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hComp

end SaturatedAtlasPresentation

end Langlands.Analytic
