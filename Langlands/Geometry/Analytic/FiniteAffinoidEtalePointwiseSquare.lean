import Langlands.Geometry.Analytic.SmallAffinoidEtalePointwiseSquare
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof

/-! # Finite affinoid pointwise etale squares without supplied algebra inputs -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    [Small.{v} (BanachSpectrum C)]
    (hf : f.IsFiniteBanach)

/-- The actual open etale part of the finite affinoid pushout, with no
supplied finite-pushout or ordinary-tensor-comparison hypothesis. -/
def finiteEtalePushout : SaturatedAtlasPresentation.{u, v, v} K :=
  etalePushout f g AffinoidPushout.finiteBanachPushout hf

/-- The first projection retains the original bounded pushout leg. -/
def finiteEtalePushoutFst : finiteEtalePushout f g hf ⟶ saturated B :=
  etalePushoutFst f g AffinoidPushout.finiteBanachPushout hf

/-- The second projection is the original changed-base map restricted to
its actual open etale source locus. -/
def finiteEtalePushoutSnd : finiteEtalePushout f g hf ⟶ saturated C :=
  etalePushoutSnd f g AffinoidPushout.finiteBanachPushout hf

theorem finiteEtalePushout_condition :
    finiteEtalePushoutFst f g hf ≫ map f =
      finiteEtalePushoutSnd f g hf ≫ map g :=
  etalePushout_condition f g AffinoidPushout.finiteBanachPushout hf

omit [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] in
/-- The second projection is etale in the localized analytic category. -/
theorem finiteEtalePushoutSnd_etale :
    SaturatedAtlasPresentation.etale
      (SaturatedAtlasPresentation.localizationFunctor.map (finiteEtalePushoutSnd f g hf)) :=
  etalePushoutSnd_etale f g AffinoidPushout.finiteBanachPushout hf
    AffinoidPushout.finiteTensorComparison

omit [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] in
/-- Its canonical saturation extension is etale on all recognized pieces. -/
theorem finiteEtalePushoutSnd_strongEtale :
    SaturatedAtlasPresentation.strongEtale (finiteEtalePushoutSnd f g hf) :=
  (SaturatedAtlasPresentation.etale_localizationFunctor_map_iff_strongEtale _).mp
    (finiteEtalePushoutSnd_etale f g hf)

include hf in
/-- A compatible point pair lifts to the actual open pushout if the original
finite map is etale at the prescribed point of its source spectrum. -/
theorem finiteEtalePushout_exists_point
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y)
    (hx : f.IsEtaleAtPoint ((spectrumHomeomorph B).symm x)) :
    ∃ t : (finiteEtalePushout f g hf).presentation.space,
      (finiteEtalePushoutFst f g hf).baseMap t = x ∧
      (finiteEtalePushoutSnd f g hf).baseMap t = y :=
  etalePushout_exists_point f g AffinoidPushout.finiteBanachPushout hf
    AffinoidPushout.finiteTensorComparison x y hxy hx

include hf in
/-- Finite affinoid pointwise base change with a strongly etale second
projection in the original, independent smallness universe. -/
theorem exists_strongEtale_pointwiseSquare_of_finiteBanach
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y)
    (hx : f.IsEtaleAtPoint ((spectrumHomeomorph B).symm x)) :
    ∃ (T : SaturatedAtlasPresentation.{u, v, v} K)
      (p : T ⟶ saturated B) (q : T ⟶ saturated C),
      p ≫ map f = q ≫ map g ∧ SaturatedAtlasPresentation.strongEtale q ∧
        ∃ t : T.presentation.space, p.baseMap t = x ∧ q.baseMap t = y := by
  obtain ⟨t, htx, hty⟩ := finiteEtalePushout_exists_point f g hf x y hxy hx
  exact ⟨finiteEtalePushout f g hf, finiteEtalePushoutFst f g hf,
    finiteEtalePushoutSnd f g hf, finiteEtalePushout_condition f g hf,
    finiteEtalePushoutSnd_strongEtale f g hf, t, htx, hty⟩

include hf in
/-- The same square has the actual localized etale predicate used by the site. -/
theorem exists_etale_pointwiseSquare_of_finiteBanach
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y)
    (hx : f.IsEtaleAtPoint ((spectrumHomeomorph B).symm x)) :
    ∃ (T : SaturatedAtlasPresentation.{u, v, v} K)
      (p : T ⟶ saturated B) (q : T ⟶ saturated C),
      p ≫ map f = q ≫ map g ∧
        SaturatedAtlasPresentation.etale (SaturatedAtlasPresentation.localizationFunctor.map q) ∧
          ∃ t : T.presentation.space, p.baseMap t = x ∧ q.baseMap t = y := by
  obtain ⟨T, p, q, hpq, hq, t, htx, hty⟩ :=
    exists_strongEtale_pointwiseSquare_of_finiteBanach f g hf x y hxy hx
  exact ⟨T, p, q, hpq, SaturatedAtlasPresentation.etale_map_of_strongEtale q hq,
    t, htx, hty⟩

end Langlands.Analytic.SmallAffinoidSpectrum
