import Langlands.Geometry.Analytic.SmallAffinoidSpectrum
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection

/-! # Small actual affinoid squares with prescribed ordinary points -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
  [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
  [Small.{v} (BanachSpectrum C)]

/-- The small realization of the actual closed-quotient affinoid pushout. -/
def pushout [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    SaturatedAtlasPresentation.{u, v, v} K :=
  saturated (AffinoidPushout.algebra f g)

/-- The first projection retains the original bounded left pushout map. -/
def pushoutFst [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    pushout f g ⟶ saturated B :=
  map (AffinoidPushout.leftMap f g)

/-- The second projection retains the original bounded right pushout map. -/
def pushoutSnd [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    pushout f g ⟶ saturated C :=
  map (AffinoidPushout.rightMap f g)

/-- The original affinoid pushout equation gives equality of complete
saturated morphisms in the independently chosen space universe. -/
theorem pushout_condition [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    pushoutFst f g ≫ map f = pushoutSnd f g ≫ map g := by
  change map (AffinoidPushout.leftMap f g) ≫ map f =
    map (AffinoidPushout.rightMap f g) ≫ map g
  rw [← map_comp, ← map_comp, AffinoidPushout.condition]

/-- Compatible ordinary points lift to the small realization of the actual
closed-quotient affinoid pushout. -/
theorem pushout_exists_point
    [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))]
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y) :
    ∃ t : (pushout f g).presentation.space,
      (pushoutFst f g).baseMap t = x ∧
      (pushoutSnd f g).baseMap t = y := by
  change ∃ t : (saturated (AffinoidPushout.algebra f g)).presentation.space,
    (map (AffinoidPushout.leftMap f g)).baseMap t = x ∧
    (map (AffinoidPushout.rightMap f g)).baseMap t = y
  let xb := (spectrumHomeomorph B).symm x
  let yc := (spectrumHomeomorph C).symm y
  have hx : spectrumHomeomorph B xb = x := (spectrumHomeomorph B).apply_symm_apply x
  have hy : spectrumHomeomorph C yc = y := (spectrumHomeomorph C).apply_symm_apply y
  have hcompat : BanachSpectrum.comap f.toBoundedRingHom xb =
      BanachSpectrum.comap g.toBoundedRingHom yc := by
    apply (spectrumHomeomorph A).injective
    rw [← map_spectrumHomeomorph, ← map_spectrumHomeomorph, hx, hy]
    exact hxy
  obtain ⟨z, hzx, hzy⟩ := AffinoidPushout.exists_point f g xb yc hcompat
  refine ⟨spectrumHomeomorph _ z, ?_, ?_⟩
  · rw [map_spectrumHomeomorph, hzx]
    exact hx
  · rw [map_spectrumHomeomorph, hzy]
    exact hy

/-- Finite Banach base change supplies the required small realization and
both complete morphisms, with their commuting equation and prescribed points.
No étaleness is asserted. -/
theorem exists_finite_pointwiseSquare
    (h : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : f.IsFiniteBanach)
    (x : (saturated B).presentation.space) (y : (saturated C).presentation.space)
    (hxy : (map f).baseMap x = (map g).baseMap y) :
    ∃ (T : SaturatedAtlasPresentation.{u, v, v} K)
      (p : T ⟶ saturated B) (q : T ⟶ saturated C) (t : T.presentation.space),
      p ≫ map f = q ≫ map g ∧ p.baseMap t = x ∧ q.baseMap t = y := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g h hf
  obtain ⟨t, htx, hty⟩ := pushout_exists_point f g x y hxy
  exact ⟨pushout f g, pushoutFst f g, pushoutSnd f g,
    t, pushout_condition f g, htx, hty⟩

end Langlands.Analytic.SmallAffinoidSpectrum
