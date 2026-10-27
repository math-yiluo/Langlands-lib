import Langlands.Geometry.Analytic.EquivariantFiniteEtaleUnder

/-! # Group restriction of relative finite étale affinoid actions -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G]
  {H : Type w} [Group H] [TopologicalSpace H]

namespace AlgebraicallyFiniteEtaleAffinoidActionUnder

/-- Restrict the group of every object and triangle under the restricted base. -/
def restrict (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
    AlgebraicallyFiniteEtaleAffinoidActionUnder X ⥤
      AlgebraicallyFiniteEtaleAffinoidActionUnder
        ((NormContinuousAffinoidAction.restrict f).obj X) :=
  (algebraicallyFiniteEtaleActionUnderProperty
    ((NormContinuousAffinoidAction.restrict f).obj X)).lift
      (inclusion X ⋙ Under.post (NormContinuousAffinoidAction.restrict f))
      (fun Y => Y.property)

@[simp]
theorem restrict_obj_baseMap (f : H →ₜ* G) {X : NormContinuousAffinoidAction K G}
    (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X) :
    ((restrict f X).obj Y).baseMap = Y.baseMap :=
  rfl

@[simp]
theorem restrict_map_homMap (f : H →ₜ* G) {X : NormContinuousAffinoidAction K G}
    {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X} (h : Y ⟶ Z) :
    homMap ((restrict f X).map h) = homMap h :=
  rfl

instance (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
    (restrict f X).Faithful where
  map_injective {Y} {Z} h k heq := by
    apply hom_ext
    exact congrArg (fun q : (restrict f X).obj Y ⟶ (restrict f X).obj Z => homMap q) heq

/-- Restriction commutes exactly with forgetting the relative base. -/
theorem restrict_forget (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
    restrict f X ⋙ forget ((NormContinuousAffinoidAction.restrict f).obj X) =
      forget X ⋙ NormContinuousAffinoidAction.restrict f :=
  rfl

/-- Forgetting all action data erases the group restriction exactly. -/
theorem restrict_forgetAction (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
    restrict f X ⋙ forgetAction ((NormContinuousAffinoidAction.restrict f).obj X) =
      forgetAction X :=
  rfl

end AlgebraicallyFiniteEtaleAffinoidActionUnder

section Spectrum

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

namespace NormContinuousAffinoidAction

/-- The identity on seminorms compares the spectrum of a restricted algebra action
with restriction of its continuous spectrum action. -/
def spectrumRestrictIso (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
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
    (X : NormContinuousAffinoidAction K G) (x : BanachSpectrum X.obj.V) :
    (spectrumRestrictIso f X).hom.hom.hom x = x :=
  rfl

@[simp]
theorem spectrumRestrictIso_inv_apply (f : H →ₜ* G)
    (X : NormContinuousAffinoidAction K G) (x : BanachSpectrum X.obj.V) :
    (spectrumRestrictIso f X).inv.hom.hom x = x :=
  rfl

/-- Spectrum commutes with group restriction by a natural identity on points. -/
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

end NormContinuousAffinoidAction

namespace AlgebraicallyFiniteEtaleAffinoidActionUnder

/-- Restrict continuous equivariant spectra over a base and identify the
restricted base with the actual spectrum of the restricted algebra action. -/
def spectrumRestrictionIso (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
    (restrict f X).op ⋙
        spectrumOverFunctor ((NormContinuousAffinoidAction.restrict f).obj X) ⋙
        Over.map (NormContinuousAffinoidAction.spectrumRestrictIso f X).hom ≅
      spectrumOverFunctor X ⋙ Over.post (ContAction.res TopCat f) :=
  NatIso.ofComponents
    (fun Y => Over.isoMk
      (NormContinuousAffinoidAction.spectrumRestrictIso f Y.unop.obj.right) (by
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
    {X : NormContinuousAffinoidAction K G}
    (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X)
    (x : BanachSpectrum Y.obj.right.obj.V) :
    ((spectrumRestrictionIso f X).hom.app (Opposite.op Y)).left.hom.hom x = x :=
  rfl

@[simp]
theorem spectrumRestrictionIso_inv_apply (f : H →ₜ* G)
    {X : NormContinuousAffinoidAction K G}
    (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X)
    (x : BanachSpectrum Y.obj.right.obj.V) :
    ((spectrumRestrictionIso f X).inv.app (Opposite.op Y)).left.hom.hom x = x :=
  rfl

end AlgebraicallyFiniteEtaleAffinoidActionUnder

end Spectrum

end Langlands.Analytic
