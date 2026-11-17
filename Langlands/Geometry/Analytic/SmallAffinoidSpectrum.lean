import Langlands.Geometry.Analytic.AffinoidSourceFunctor
import Langlands.Geometry.Analytic.AtlasHomeomorph
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Statement
import Mathlib.Topology.Instances.Shrink

/-! # Actual affinoid spectra in an independent small space universe -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual spectrum, transported to its supplied small universe. -/
def presentation (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    AffinoidAtlasPresentation.{u, v, 0} K where
  space := TopCat.of (Shrink.{v} (BanachSpectrum R))
  atlas := (PresentedAffinoidSpace.singletonAtlas (Opposite.op R)).transport
    (Shrink.homeomorph (BanachSpectrum R))

/-- The canonical homeomorphism retains every ordinary spectrum point. -/
def spectrumHomeomorph (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    BanachSpectrum R ≃ₜ (presentation R).space :=
  Shrink.homeomorph (BanachSpectrum R)

/-- The bounded map on the original algebras gives all admissible singleton
pullbacks, before saturation. -/
def strongMap {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) : StrongHom (presentation S) (presentation R) where
  baseMap := (⟨spectrumHomeomorph R, (spectrumHomeomorph R).continuous⟩ :
    C(BanachSpectrum R, (presentation R).space)).comp
    ((BanachSpectrum.comapContinuous f.toBoundedRingHom).comp
      ⟨(spectrumHomeomorph S).symm, (spectrumHomeomorph S).symm.continuous⟩)
  target_exists _ := ⟨PUnit.unit, by
    intro x _
    exact ⟨(spectrumHomeomorph R).symm x, (spectrumHomeomorph R).apply_symm_apply x⟩⟩
  pullback _ _ _ := f
  chart_comm _ _ _ x := by
    change BanachSpectrum S at x
    change spectrumHomeomorph R (BanachSpectrum.comap f.toBoundedRingHom x) =
      spectrumHomeomorph R (BanachSpectrum.comap f.toBoundedRingHom
        ((spectrumHomeomorph S).symm (spectrumHomeomorph S x)))
    rw [Homeomorph.symm_apply_apply]
  restriction_comm _ _ _ _ _ _ _ _ := rfl

/-- Singleton target indices make coefficient compatibility automatic. -/
theorem strongMap_coherent {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) : (strongMap f).HasCoherentPullbacks := by
  intro i j k hj hk T η m hmj hmk α hα
  cases j
  cases k
  exact hα.symm

/-- The complete original map with its coefficient compatibility. -/
def compatibleMap {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) : CompatibleStrongHom (presentation S) (presentation R) where
  toStrongHom := strongMap f
  compatible := (strongMap f).hasLocallyCompatiblePullbacks_iff.mpr (strongMap_coherent f)

/-- The original singleton maps preserve identity. -/
theorem compatibleMap_id (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    compatibleMap (BoundedAlgHom.id K R) = CompatibleStrongHom.id (presentation R) := by
  refine CompatibleStrongHom.ext_of_pullback ?hb ?hp
  · apply ContinuousMap.ext
    intro x
    change spectrumHomeomorph R
      (BanachSpectrum.comap (BoundedAlgHom.id K R).toBoundedRingHom
        ((spectrumHomeomorph R).symm x)) = x
    have h (s : BanachSpectrum R) :
        BanachSpectrum.comap (BoundedAlgHom.id K R).toBoundedRingHom s = s :=
      BanachSpectrum.ext (fun _ => rfl)
    rw [h, Homeomorph.apply_symm_apply]
  · intro i
    refine ⟨PUnit.unit, ?_, ?_⟩
    · intro x _
      exact ⟨(spectrumHomeomorph R).symm x, (spectrumHomeomorph R).apply_symm_apply x⟩
    rfl

/-- Composition retains the complete original bounded maps. -/
theorem compatibleMap_comp {R S T : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    [Small.{v} (BanachSpectrum T)]
    (f : BoundedAlgHom K R S) (g : BoundedAlgHom K S T) :
    compatibleMap (g.comp f) = (compatibleMap g).comp (compatibleMap f) := by
  refine CompatibleStrongHom.ext_of_pullback ?hb ?hp
  · apply ContinuousMap.ext
    intro x
    change spectrumHomeomorph R
      (BanachSpectrum.comap (g.comp f).toBoundedRingHom
        ((spectrumHomeomorph T).symm x)) =
      spectrumHomeomorph R (BanachSpectrum.comap f.toBoundedRingHom
        ((spectrumHomeomorph S).symm (spectrumHomeomorph S
          (BanachSpectrum.comap g.toBoundedRingHom ((spectrumHomeomorph T).symm x)))))
    rw [Homeomorph.symm_apply_apply]
    rfl
  · intro i
    have hf : (strongMap f).baseMap '' Set.range ((presentation S).atlas.chart PUnit.unit) ⊆
        Set.range ((presentation R).atlas.chart PUnit.unit) := by
      intro x _
      exact ⟨(spectrumHomeomorph R).symm x, (spectrumHomeomorph R).apply_symm_apply x⟩
    have hg : (strongMap g).baseMap '' Set.range ((presentation T).atlas.chart i) ⊆
        Set.range ((presentation S).atlas.chart PUnit.unit) := by
      intro x _
      exact ⟨(spectrumHomeomorph S).symm x, (spectrumHomeomorph S).apply_symm_apply x⟩
    have hgf : (strongMap (g.comp f)).baseMap '' Set.range ((presentation T).atlas.chart i) ⊆
        Set.range ((presentation R).atlas.chart PUnit.unit) := by
      intro x _
      exact ⟨(spectrumHomeomorph R).symm x, (spectrumHomeomorph R).apply_symm_apply x⟩
    refine ⟨PUnit.unit, hgf, ?_⟩
    rw [CompatibleStrongHom.comp_pullback (compatibleMap g) (compatibleMap f)
      i PUnit.unit PUnit.unit hg hf]
    rfl

/-- Saturation uses exactly the independently chosen space universe. -/
def saturated (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    SaturatedAtlasPresentation.{u, v, v} K :=
  SaturatedAtlasPresentation.ofSaturation (presentation R)

/-- The actual bounded map extended to all local full domains. -/
def map {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) : saturated S ⟶ saturated R :=
  (compatibleMap f).saturationExtension

@[simp]
theorem map_spectrumHomeomorph {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) (s : BanachSpectrum S) :
    (map f).baseMap (spectrumHomeomorph S s) =
      spectrumHomeomorph R (BanachSpectrum.comap f.toBoundedRingHom s) := by
  change spectrumHomeomorph R (BanachSpectrum.comap f.toBoundedRingHom
    ((spectrumHomeomorph S).symm (spectrumHomeomorph S s))) = _
  rw [Homeomorph.symm_apply_apply]

@[simp]
theorem map_id (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    map (BoundedAlgHom.id K R) = 𝟙 (saturated R) := by
  change CompatibleAtlasPresentation.saturationFunctor.map (compatibleMap _) = _
  rw [compatibleMap_id]
  exact CompatibleAtlasPresentation.saturationFunctor.map_id ⟨presentation R⟩

@[simp]
theorem map_comp {R S T : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    [Small.{v} (BanachSpectrum T)]
    (f : BoundedAlgHom K R S) (g : BoundedAlgHom K S T) :
    map (g.comp f) = map g ≫ map f := by
  change CompatibleAtlasPresentation.saturationFunctor.map (compatibleMap _) = _
  rw [compatibleMap_comp]
  exact CompatibleAtlasPresentation.saturationFunctor.map_comp (compatibleMap g) (compatibleMap f)

end Langlands.Analytic.SmallAffinoidSpectrum
