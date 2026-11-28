import Langlands.Geometry.Analytic.FiniteAffinoidLocalizedHomDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachBounds
import Langlands.Geometry.Analytic.SmallAffinoidPullbacks
import Mathlib.Algebra.Algebra.Epi

/-! # Finite Banach monomorphisms of affinoid spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open PresentedAffinoidAlgebra AffinoidPushout SaturatedAtlasPresentation
open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}
  [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]

/-- An affinoid monomorphism induced by a finite Banach map has a surjective
map of algebras. -/
theorem surjective_of_finiteBanach_mono (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    [Mono (localizedMapEquiv.{u, v} A B f)] : Function.Surjective f := by
  let : Small.{v} (BanachSpectrum (algebra f f)) :=
    small_spectrum_of_finiteBanachPushout f f finiteBanachPushout hf
  have h := (pushout_localized_isPullback.{u, v} f f).w
  change localizedMapEquiv.{u, v} B _ (leftMap f f) ≫ localizedMapEquiv.{u, v} A B f =
    localizedMapEquiv.{u, v} B _ (rightMap f f) ≫ localizedMapEquiv.{u, v} A B f at h
  have heq := (localizedMapEquiv.{u, v} B (algebra f f)).injective
    ((cancel_mono (localizedMapEquiv.{u, v} A B f)).mp h)
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Module.Finite A B := hf.finite
  apply (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := A) (A := B)).mp
  apply (Algebra.isEpi_iff_forall_one_tmul_eq A B).mpr
  intro b
  apply (tensorComparison_bijective f f hf).1
  change tensorComparison f f (tensorRight f f b) =
    tensorComparison f f (tensorLeft f f b)
  rw [tensorComparison_tensorRight, tensorComparison_tensorLeft, heq]

/-- The localized isomorphism of a finite Banach monomorphism with flat
algebra map and surjective point map. -/
def isoOfFiniteBanachMonoOfFlatOfSpectrumSurjective
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    [Mono (localizedMapEquiv.{u, v} A B f)] :
    localizationFunctor.obj (saturated.{u, v} B) ≅
      localizationFunctor.obj (saturated.{u, v} A) := by
  have hinj : Function.Injective f :=
    (faithfullyFlat_of_flat_of_spectrum_surjective f hflat hsurj).injective
  let e := AlgEquiv.ofBijective f.toAlgHom ⟨hinj, surjective_of_finiteBanach_mono f hf⟩
  let g := BoundedAlgHom.ofFiniteBanachTriangle f hf (BoundedAlgHom.id K A) e.symm.toAlgHom
    (AlgHom.ext e.symm_apply_apply)
  have hgf : g.comp f = BoundedAlgHom.id K A :=
    BoundedAlgHom.ext e.symm_apply_apply
  have hfg : f.comp g = BoundedAlgHom.id K B :=
    BoundedAlgHom.ext e.apply_symm_apply
  refine ⟨localizedMapEquiv.{u, v} A B f, localizedMapEquiv.{u, v} B A g, ?_, ?_⟩
  · rw [← localizedMapEquiv_comp, hfg, localizedMapEquiv_apply, map_id]
    exact localizationFunctor.map_id _
  · rw [← localizedMapEquiv_comp, hgf, localizedMapEquiv_apply, map_id]
    exact localizationFunctor.map_id _

@[simp]
theorem isoOfFiniteBanachMonoOfFlatOfSpectrumSurjective_hom
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    [Mono (localizedMapEquiv.{u, v} A B f)] :
    (isoOfFiniteBanachMonoOfFlatOfSpectrumSurjective.{u, v} f hf hflat hsurj).hom =
      localizedMapEquiv.{u, v} A B f := rfl

theorem isIso_of_finiteBanach_mono_of_flat_of_spectrum_surjective
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    [Mono (localizedMapEquiv.{u, v} A B f)] : IsIso (localizedMapEquiv.{u, v} A B f) := by
  rw [← isoOfFiniteBanachMonoOfFlatOfSpectrumSurjective_hom f hf hflat hsurj]
  infer_instance

end Langlands.Analytic.SmallAffinoidSpectrum
