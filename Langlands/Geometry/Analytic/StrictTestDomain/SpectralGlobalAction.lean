import Langlands.Geometry.Analytic.StrictTestDomain.SpectralLocalContinuityProof
import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits
import Langlands.Geometry.Analytic.RationalIdentity
import Langlands.Geometry.Analytic.NormContinuousAction

/-! # The global continuous spectrum action for rational spectral operators -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory

namespace RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedStrictAffinoidAlgebra K)

/-- The empty rational quotient's actual structural spectrum map is a
homeomorphism onto the original spectrum. -/
def wholeSpectrumHomeomorph :
    BanachSpectrum (whole K P).algebra ≃ₜ BanachSpectrum P :=
  (RationalIdentity.emptyEquiv K P).spectrumHomeomorph

@[simp]
theorem wholeSpectrumHomeomorph_apply (x : BanachSpectrum (whole K P).algebra) :
    wholeSpectrumHomeomorph P x = (whole K P).spectrumMap x := rfl

end RationalData

namespace RationalAutomorphism.RationalSpectralAction

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- Every operator stabilizes the actual whole rational locus. -/
theorem mem_wholeLocusOpenSubgroup (g : G) :
    g ∈ ρ.locusOpenSubgroup (RationalData.whole K P) := by
  rw [mem_locusOpenSubgroup, RationalData.locus_whole, Set.image_univ]
  exact Set.range_eq_univ.mpr (MulAction.surjective (ρ.toMonoidHom g))

/-- Continuous inclusion into the stabilizer of the whole rational locus. -/
def wholeStabilizerHom : G →ₜ* ρ.locusOpenSubgroup (RationalData.whole K P) where
  toFun g := ⟨g, ρ.mem_wholeLocusOpenSubgroup g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk _

@[simp]
theorem wholeStabilizerHom_coe (g : G) : (ρ.wholeStabilizerHom g : G) = g := rfl

/-- On the whole quotient, the original spectrum action is conjugate to the
proved local inverse-pullback action by the actual structural homeomorphism. -/
theorem wholeSpectrumHomeomorph_smul (g : G)
    (x : BanachSpectrum (RationalData.whole K P).algebra) :
    RationalData.wholeSpectrumHomeomorph P
        ((ρ.sectionAction (RationalData.whole K P) (ρ.wholeStabilizerHom g)) • x) =
      ρ.toMonoidHom g • RationalData.wholeSpectrumHomeomorph P x := by
  apply BanachSpectrum.ext
  intro a
  have h := ρ.sectionAction_baseMap (RationalData.whole K P)
    ((ρ.wholeStabilizerHom g)⁻¹) a
  rw [map_inv] at h
  have hg : ρ.toMonoidHom
      (((ρ.wholeStabilizerHom g)⁻¹ :
        ρ.locusOpenSubgroup (RationalData.whole K P)) : G) =
      (ρ.toMonoidHom g)⁻¹ := by simp
  rw [hg] at h
  exact congrArg (fun b : (RationalData.whole K P).algebra => x b) h

/-- Continuity in the restricted rational spectral topology implies joint
continuity on the entire actual affinoid spectrum, without norm-continuous
algebra orbits. -/
theorem continuous_globalSpectrumAction :
    Continuous (fun p : G × BanachSpectrum P => ρ.toMonoidHom p.1 • p.2) := by
  let e := RationalData.wholeSpectrumHomeomorph P
  have hlocal := (rationalSpectralLocalContinuity K P G ρ
    (RationalData.whole K P)).2.2
  have hinput : Continuous (fun p : G × BanachSpectrum P =>
      (ρ.wholeStabilizerHom p.1, e.symm p.2)) :=
    (ρ.wholeStabilizerHom.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd)
  have h := e.continuous.comp (hlocal.comp hinput)
  convert h using 1
  funext p
  exact ((ρ.wholeSpectrumHomeomorph_smul p.1 (e.symm p.2)).trans
    (congrArg (fun x : BanachSpectrum P => ρ.toMonoidHom p.1 • x)
      (e.apply_symm_apply p.2))).symm

/-- The original inverse bounded maps supply the global categorical action. -/
def globalSpectrumAction : Action TopCat.{u} G where
  V := TopCat.of (BanachSpectrum P)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        (BanachSpectrum.comapContinuous (ρ.toMonoidHom g).inv.toBoundedRingHom)
      map_one' := by
        apply TopCat.ext
        intro x
        change ρ.toMonoidHom 1 • x = x
        simp
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        change ρ.toMonoidHom (g * h) • x =
          ρ.toMonoidHom g • (ρ.toMonoidHom h • x)
        rw [map_mul, mul_smul] }

/-- The actual whole affinoid spectrum as a continuous G-action. -/
def globalSpectrum : ContAction TopCat.{u} G :=
  ⟨ρ.globalSpectrumAction, (Action.isContinuous_def _).mpr
    ρ.continuous_globalSpectrumAction⟩

@[simp]
theorem globalSpectrum_apply (g : G) (x : BanachSpectrum P) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (ρ.globalSpectrum.obj.ρ g) x) a =
        x ((ρ.toMonoidHom g).inv.toAlgHom a) := rfl

end RationalAutomorphism.RationalSpectralAction

end Langlands.Analytic.StrictTestDomain
