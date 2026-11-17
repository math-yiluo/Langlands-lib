import Langlands.Geometry.Analytic.SmallAffinoidEtaleRealization

/-! # Actual finite small affinoid étale base-change squares -/

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

/-- The actual affinoid pushout with its smallness supplied by the finite leg. -/
def finitePushout : SaturatedAtlasPresentation.{u, v, v} K :=
  letI := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  pushout f g

/-- The first actual pushout leg in the small saturated category. -/
def finitePushoutFst : finitePushout f g hpush hf ⟶ saturated B :=
  letI := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  pushoutFst f g

/-- The changed-base projection, with its unchanged bounded algebra map. -/
def finitePushoutSnd : finitePushout f g hpush hf ⟶ saturated C :=
  letI := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  pushoutSnd f g

theorem finitePushout_condition :
    finitePushoutFst f g hpush hf ≫ map f = finitePushoutSnd f g hpush hf ≫ map g := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  exact pushout_condition f g

omit [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] in
/-- Tensor comparison gives pointwise étaleness everywhere on the actual
finite pushout, hence the projection is canonically strong étale. -/
theorem finitePushoutSnd_strongEtale
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (het : ∀ x, f.IsEtaleAtPoint x) :
    SaturatedAtlasPresentation.strongEtale (finitePushoutSnd f g hpush hf) := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  exact map_strongEtale_of_finite_pointwiseEtale (AffinoidPushout.rightMap f g)
    hpush htensor (hpush _ _ _ f g hf) fun x =>
      AffinoidPushout.rightMap_isEtaleAtPoint_of_tensorComparison f g
        (htensor _ _ _ f g hf) hf.finite.finiteType x (het _)

omit [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] in
/-- The second projection is étale for the actual localized analytic category. -/
theorem finitePushoutSnd_etale
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (het : ∀ x, f.IsEtaleAtPoint x) :
    SaturatedAtlasPresentation.etale (SaturatedAtlasPresentation.localizationFunctor.map
      (finitePushoutSnd f g hpush hf)) :=
  SaturatedAtlasPresentation.etale_map_of_strongEtale _
    (finitePushoutSnd_strongEtale f g hpush hf htensor het)

include hpush hf in
/-- Compatible prescribed points lift to an actual small commuting square whose
changed-base projection is étale in the localized category used by the site. -/
theorem exists_finite_etale_pointwiseSquare
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (het : ∀ x, f.IsEtaleAtPoint x)
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y) :
    ∃ (T : SaturatedAtlasPresentation.{u, v, v} K)
      (p : T ⟶ saturated B) (q : T ⟶ saturated C),
      p ≫ map f = q ≫ map g ∧
        SaturatedAtlasPresentation.etale (SaturatedAtlasPresentation.localizationFunctor.map q) ∧
          ∃ t : T.presentation.space, p.baseMap t = x ∧ q.baseMap t = y := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g hpush hf
  obtain ⟨t, htx, hty⟩ := pushout_exists_point f g x y hxy
  exact ⟨finitePushout f g hpush hf, finitePushoutFst f g hpush hf,
    finitePushoutSnd f g hpush hf, finitePushout_condition f g hpush hf,
    finitePushoutSnd_etale f g hpush hf htensor het, t, htx, hty⟩

end Langlands.Analytic.SmallAffinoidSpectrum
