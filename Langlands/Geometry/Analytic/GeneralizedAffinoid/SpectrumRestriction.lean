import Langlands.Geometry.Analytic.GeneralizedAffinoid.NormContinuousAction

/-! # Continuous group restriction of positive-polyradius spectra -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

namespace NormContinuousAction

/-- The identity on seminorms identifies the spectrum of a restricted quotient
action with restriction of its continuous spectrum action. -/
def spectrumRestrictIso (f : H →ₜ* G) (X : NormContinuousAction K G) :
    spectrum ((restrict f).obj X) ≅ (ContAction.res TopCat f).obj (spectrum X) :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) (by
    intro h
    apply TopCat.ext
    intro x
    change BanachSpectrum X.obj.V at x
    apply BanachSpectrum.ext
    intro a
    change x ((X.obj.ρ (f (h⁻¹))).toAlgHom a) =
      x ((X.obj.ρ ((f h)⁻¹)).toAlgHom a)
    rw [map_inv]))

@[simp]
theorem spectrumRestrictIso_hom_apply (f : H →ₜ* G)
    (X : NormContinuousAction K G) (x : BanachSpectrum X.obj.V) :
    (spectrumRestrictIso f X).hom.hom.hom x = x :=
  rfl

@[simp]
theorem spectrumRestrictIso_inv_apply (f : H →ₜ* G)
    (X : NormContinuousAction K G) (x : BanachSpectrum X.obj.V) :
    (spectrumRestrictIso f X).inv.hom.hom x = x :=
  rfl

/-- Spectrum commutes naturally with continuous group restriction, with identity
components on the actual bounded multiplicative seminorms. -/
def spectrumRestrictionIso (f : H →ₜ* G) :
    (restrict (K := K) f).op ⋙ spectrumFunctor ≅
      spectrumFunctor ⋙ ContAction.res TopCat f :=
  NatIso.ofComponents (fun X => spectrumRestrictIso f X.unop) (by
    intro X Y h
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    rfl)

end NormContinuousAction

end Langlands.Analytic.PresentedAffinoidAlgebra
