import Langlands.Geometry.Analytic.GeneralizedAffinoid.EquivariantFiniteEtaleUnder
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumRestriction

/-! # Group restriction of relative finite étale positive-polyradius actions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G]
  {H : Type w} [Group H] [TopologicalSpace H]

namespace AlgebraicallyFiniteEtaleActionUnder

/-- Restrict the acting group, retaining every actual relative bounded map. -/
def restrict (f : H →ₜ* G) (X : NormContinuousAction K G) :
    AlgebraicallyFiniteEtaleActionUnder X ⥤
      AlgebraicallyFiniteEtaleActionUnder
        ((NormContinuousAction.restrict f).obj X) :=
  (algebraicallyFiniteEtaleActionUnderProperty
    ((NormContinuousAction.restrict f).obj X)).lift
      (inclusion X ⋙ Under.post (NormContinuousAction.restrict f))
      (fun Y => Y.property)

@[simp]
theorem restrict_obj_baseMap (f : H →ₜ* G) {X : NormContinuousAction K G}
    (Y : AlgebraicallyFiniteEtaleActionUnder X) :
    ((restrict f X).obj Y).baseMap = Y.baseMap :=
  rfl

@[simp]
theorem restrict_map_homMap (f : H →ₜ* G) {X : NormContinuousAction K G}
    {Y Z : AlgebraicallyFiniteEtaleActionUnder X} (h : Y ⟶ Z) :
    homMap ((restrict f X).map h) = homMap h :=
  rfl

instance (f : H →ₜ* G) (X : NormContinuousAction K G) :
    (restrict f X).Faithful where
  map_injective {Y} {Z} h k heq := by
    apply hom_ext
    exact congrArg (fun q : (restrict f X).obj Y ⟶ (restrict f X).obj Z => homMap q) heq

/-- Forgetting the relative structural map commutes exactly with restriction. -/
theorem restrict_forget (f : H →ₜ* G) (X : NormContinuousAction K G) :
    restrict f X ⋙ forget ((NormContinuousAction.restrict f).obj X) =
      forget X ⋙ NormContinuousAction.restrict f :=
  rfl

/-- Forgetting all action data erases group restriction exactly. -/
theorem restrict_forgetAction (f : H →ₜ* G) (X : NormContinuousAction K G) :
    restrict f X ⋙ forgetAction ((NormContinuousAction.restrict f).obj X) =
      forgetAction X :=
  rfl

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Relative spectra commute with restriction after identifying the spectrum
of the restricted base with restriction of the original base spectrum. -/
def spectrumRestrictionIso (f : H →ₜ* G) (X : NormContinuousAction K G) :
    (restrict f X).op ⋙
        spectrumOverFunctor ((NormContinuousAction.restrict f).obj X) ⋙
        Over.map (NormContinuousAction.spectrumRestrictIso f X).hom ≅
      spectrumOverFunctor X ⋙ Over.post (ContAction.res TopCat f) :=
  NatIso.ofComponents
    (fun Y => Over.isoMk
      (NormContinuousAction.spectrumRestrictIso f Y.unop.obj.right) (by
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply TopCat.ext
        intro x
        rfl))
    (by
      intro Y Z h
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      rfl)

@[simp]
theorem spectrumRestrictionIso_hom_apply (f : H →ₜ* G)
    {X : NormContinuousAction K G}
    (Y : AlgebraicallyFiniteEtaleActionUnder X)
    (x : BanachSpectrum Y.obj.right.obj.V) :
    ((spectrumRestrictionIso f X).hom.app (Opposite.op Y)).left.hom.hom x = x :=
  rfl

@[simp]
theorem spectrumRestrictionIso_inv_apply (f : H →ₜ* G)
    {X : NormContinuousAction K G}
    (Y : AlgebraicallyFiniteEtaleActionUnder X)
    (x : BanachSpectrum Y.obj.right.obj.V) :
    ((spectrumRestrictionIso f X).inv.app (Opposite.op Y)).left.hom.hom x = x :=
  rfl

end Spectrum

end AlgebraicallyFiniteEtaleActionUnder

end Langlands.Analytic.PresentedAffinoidAlgebra
