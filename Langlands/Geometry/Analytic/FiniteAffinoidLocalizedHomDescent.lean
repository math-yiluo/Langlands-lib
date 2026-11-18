import Langlands.Geometry.Analytic.FiniteFaithfullyFlatBoundedDescent
import Langlands.Geometry.Analytic.SmallAffinoidLocalizedMaps
import Langlands.Geometry.Analytic.SmallAffinoidEtaleBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Mathlib.RingTheory.RingHom.Flat

/-! # Localized Hom descent for a finite flat affinoid cover -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra SaturatedAtlasPresentation AffinoidPushout

section FaithfulFlatness

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A flat affinoid map that is surjective on spectra is faithfully flat.
Every proper ideal is detected by an actual spectrum point. -/
theorem faithfullyFlat_of_flat_of_spectrum_surjective
    {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B)
    (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)) :
    f.toAlgHom.toRingHom.FaithfullyFlat := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  change Module.FaithfullyFlat A B
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal A B).2 ⟨hflat, ?_⟩
  intro I hI htop
  obtain ⟨x, hx⟩ := exists_spectrum_kernel_of_proper_ideal A I hI
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : I.map (algebraMap A B) ≤ y.kernel := Ideal.map_le_iff_le_comap.mpr hx
  have hone : (1 : B) ∈ I • (⊤ : Submodule A B) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Ideal.smul_top_eq_map] at hone
  change (1 : B) ∈ I.map (algebraMap A B) at hone
  exact y.kernel_isPrime.ne_top ((Ideal.eq_top_iff_one y.kernel).mpr (hy hone))

end FaithfulFlatness

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Descent across the actual localized self-pullback of a single finite flat
surjective affinoid morphism, with a small affinoid target. -/
def FiniteAffinoidLocalizedHomDescentStatement : Prop :=
  ∀ {A B C : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    [Small.{v} (BanachSpectrum C)]
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach),
    f.toAlgHom.toRingHom.Flat →
    Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom) →
    ∀ (g : localizationFunctor.obj (saturated.{u, v} B) ⟶
        localizationFunctor.obj (saturated.{u, v} C)),
      localizationFunctor.map (finitePushoutFst f f finiteBanachPushout hf) ≫ g =
        localizationFunctor.map (finitePushoutSnd f f finiteBanachPushout hf) ≫ g →
      ∃! h : localizationFunctor.obj (saturated A) ⟶ localizationFunctor.obj (saturated C),
        localizationFunctor.map (map f) ≫ h = g

theorem finiteAffinoidLocalizedHomDescent :
    FiniteAffinoidLocalizedHomDescentStatement.{u, v} K := by
  intro A B C _ _ _ f hf hflat hsurj g hmatch
  let : Small.{v} (BanachSpectrum (algebra f f)) :=
    small_spectrum_of_finiteBanachPushout f f finiteBanachPushout hf
  let g₀ := (localizedMapEquiv.{u, v} C B).symm g
  have hg₀ : localizedMapEquiv.{u, v} C B g₀ = g :=
    (localizedMapEquiv.{u, v} C B).apply_symm_apply g
  have hgMatch : (leftMap f f).comp g₀ = (rightMap f f).comp g₀ := by
    apply (localizedMapEquiv.{u, v} C (algebra f f)).injective
    rw [localizedMapEquiv_comp, localizedMapEquiv_comp, hg₀]
    exact hmatch
  obtain ⟨h, hh, huniq⟩ := finiteFaithfullyFlatBoundedDescent K f g₀ hf
    (faithfullyFlat_of_flat_of_spectrum_surjective f hflat hsurj) hgMatch
  refine ⟨localizedMapEquiv.{u, v} C A h, ?_, ?_⟩
  · change localizedMapEquiv.{u, v} A B f ≫ localizedMapEquiv.{u, v} C A h = g
    rw [← localizedMapEquiv_comp, hh, hg₀]
  · intro h' hh'
    obtain ⟨h₀', rfl⟩ := (localizedMapEquiv.{u, v} C A).surjective h'
    apply congrArg (localizedMapEquiv.{u, v} C A)
    apply huniq
    apply (localizedMapEquiv.{u, v} C B).injective
    rw [localizedMapEquiv_comp]
    exact hh'.trans hg₀.symm

end Langlands.Analytic.SmallAffinoidSpectrum
