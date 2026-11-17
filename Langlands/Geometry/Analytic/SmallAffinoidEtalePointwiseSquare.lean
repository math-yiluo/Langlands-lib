import Langlands.Geometry.Analytic.SmallAffinoidEtaleNeighborhood

/-! # Small affine étale squares at a prescribed ordinary point -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    [Small.{v} (BanachSpectrum C)]
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : f.IsFiniteBanach)

/-- The actual open étale part of the finite small affinoid pushout. -/
def etalePushout : SaturatedAtlasPresentation.{u, v, v} K :=
  letI := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  etaleOpenSpace (AffinoidPushout.rightMap f g) (hpush _ _ _ f g hf)

/-- The actual inclusion into the full small affinoid pushout. -/
def etalePushoutInclusion : etalePushout f g hpush hf ⟶ finitePushout f g hpush hf :=
  letI := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  (saturated (AffinoidPushout.algebra f g)).domainInclusion
    ((saturated (AffinoidPushout.algebra f g)).openDomain
      (etaleOpenSet (AffinoidPushout.rightMap f g))
      (isOpen_etaleOpenSet (AffinoidPushout.rightMap f g) (hpush _ _ _ f g hf)))

/-- The first restricted projection retains the complete first bounded leg. -/
def etalePushoutFst : etalePushout f g hpush hf ⟶ saturated B :=
  etalePushoutInclusion f g hpush hf ≫ finitePushoutFst f g hpush hf

/-- The actual second projection restricted to its open étale part. -/
def etalePushoutSnd : etalePushout f g hpush hf ⟶ saturated C :=
  letI := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  etaleOpenMap (AffinoidPushout.rightMap f g) (hpush _ _ _ f g hf)

theorem etalePushout_condition :
    etalePushoutFst f g hpush hf ≫ map f = etalePushoutSnd f g hpush hf ≫ map g := by
  change (etalePushoutInclusion f g hpush hf ≫ finitePushoutFst f g hpush hf) ≫ map f =
    (etalePushoutInclusion f g hpush hf ≫ finitePushoutSnd f g hpush hf) ≫ map g
  rw [Category.assoc, Category.assoc, finitePushout_condition f g hpush hf]

omit [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] in
/-- The restricted second projection has the actual localized étale predicate. -/
theorem etalePushoutSnd_etale
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K) :
    SaturatedAtlasPresentation.etale (SaturatedAtlasPresentation.localizationFunctor.map
      (etalePushoutSnd f g hpush hf)) := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  exact etaleOpenMap_etale (AffinoidPushout.rightMap f g) hpush htensor (hpush _ _ _ f g hf)

include hpush hf in
/-- At any compatible ordinary pair where the finite leg is étale, the actual
open pushout has a point over that pair. No global étaleness is needed. -/
theorem etalePushout_exists_point
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y)
    (hx : f.IsEtaleAtPoint ((spectrumHomeomorph B).symm x)) :
    ∃ t : (etalePushout f g hpush hf).presentation.space,
      (etalePushoutFst f g hpush hf).baseMap t = x ∧
      (etalePushoutSnd f g hpush hf).baseMap t = y := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  let xb := (spectrumHomeomorph B).symm x
  let yc := (spectrumHomeomorph C).symm y
  have hxb : spectrumHomeomorph B xb = x := (spectrumHomeomorph B).apply_symm_apply x
  have hyc : spectrumHomeomorph C yc = y := (spectrumHomeomorph C).apply_symm_apply y
  have hcompat : BanachSpectrum.comap f.toBoundedRingHom xb =
      BanachSpectrum.comap g.toBoundedRingHom yc := by
    apply (spectrumHomeomorph A).injective
    rw [← map_spectrumHomeomorph, ← map_spectrumHomeomorph, hxb, hyc]
    exact hxy
  obtain ⟨z, hzx, hzy⟩ := AffinoidPushout.exists_point f g xb yc hcompat
  have hz : (AffinoidPushout.rightMap f g).IsEtaleAtPoint z :=
    AffinoidPushout.rightMap_isEtaleAtPoint_of_tensorComparison f g
      (htensor _ _ _ f g hf) hf.finite.finiteType z (hzx.symm ▸ hx)
  let t : (etalePushout f g hpush hf).presentation.space :=
    ⟨spectrumHomeomorph (AffinoidPushout.algebra f g) z, ⟨z, hz, rfl⟩⟩
  refine ⟨t, ?_, ?_⟩
  · change (map (AffinoidPushout.leftMap f g)).baseMap
      (spectrumHomeomorph (AffinoidPushout.algebra f g) z) = x
    rw [map_spectrumHomeomorph, hzx]
    exact hxb
  · change (map (AffinoidPushout.rightMap f g)).baseMap
      (spectrumHomeomorph (AffinoidPushout.algebra f g) z) = y
    rw [map_spectrumHomeomorph, hzy]
    exact hyc

include hpush hf in
/-- Point-dependent finite affine étale base change in independent universes. -/
theorem exists_etale_pointwiseSquare_of_finite
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y)
    (hx : f.IsEtaleAtPoint ((spectrumHomeomorph B).symm x)) :
    ∃ (T : SaturatedAtlasPresentation.{u, v, v} K)
      (p : T ⟶ saturated B) (q : T ⟶ saturated C),
      p ≫ map f = q ≫ map g ∧
        SaturatedAtlasPresentation.etale (SaturatedAtlasPresentation.localizationFunctor.map q) ∧
          ∃ t : T.presentation.space, p.baseMap t = x ∧ q.baseMap t = y := by
  obtain ⟨t, htx, hty⟩ := etalePushout_exists_point f g hpush hf htensor x y hxy hx
  exact ⟨etalePushout f g hpush hf, etalePushoutFst f g hpush hf,
    etalePushoutSnd f g hpush hf, etalePushout_condition f g hpush hf,
    etalePushoutSnd_etale f g hpush hf htensor, t, htx, hty⟩

end Langlands.Analytic.SmallAffinoidSpectrum
