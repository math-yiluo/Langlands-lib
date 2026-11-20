import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Mathlib.Data.Finset.NoncommProd
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! Topology and right Haar invariance for the ambient groups in cyclic base change. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix MeasureTheory Topology
open scoped NNReal

universe u v

section Topology

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]

/-- A finite algebra with the module topology has the topological properties of a finite
product of copies of the local field. -/
theorem finiteAlgebraTopology [Module.Finite F E] :
    T2Space E ∧ LocallyCompactSpace E ∧ SecondCountableTopology E := by
  let _ := LocalFieldTopology.t2Space F
  let _ := LocalFieldTopology.secondCountableTopology F
  let b := Module.finBasis F E
  let e : E ≃ₜ (Fin (Module.finrank F E) → F) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  exact ⟨e.symm.t2Space, e.locallyCompactSpace_iff.mpr inferInstance,
    e.secondCountableTopology⟩

/-- Coefficient extension is a closed embedding on general linear groups. -/
theorem generalLinear_isClosedEmbedding_algebraMap [T2Space E] [Nontrivial E] (n : ℕ) :
    IsClosedEmbedding (GeneralLinearGroup.map (n := Fin n) (algebraMap F E)) := by
  let _ := LocalFieldTopology.t2Space F
  let f : F →ₗ[F] E := (Algebra.ofId F E).toLinearMap
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have hleft : Function.LeftInverse r f := LinearMap.congr_fun hr
  exact (hleft.isClosedEmbedding (IsModuleTopology.continuous_of_linearMap r)
    (IsModuleTopology.continuous_of_linearMap f)).generalLinearGroup_map

end Topology

section Haar

variable (R : Type v) [CommRing R] [IsArtinianRing R] [IsReduced R] (n : ℕ)

/-- General linear groups over reduced Artinian rings decompose by residue fields. -/
def generalLinearResidueEquiv :
    GeneralLinear n R ≃* ∀ I : MaximalSpectrum R, GeneralLinear n (R ⧸ I.asIdeal) :=
  (Units.mapEquiv
    (((IsArtinianRing.equivPi R).toRingEquiv.mapMatrix (m := Fin n)).trans
      Matrix.piRingEquiv).toMulEquiv).trans MulEquiv.piUnits

theorem generalLinearResidueEquiv_apply (g : GeneralLinear n R) (I : MaximalSpectrum R) :
    generalLinearResidueEquiv R n g I = GeneralLinearGroup.map (Ideal.Quotient.mk I.asIdeal) g :=
  rfl

variable [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace (GeneralLinear n R)]
  [MeasurableSpace (GeneralLinear n R)] [BorelSpace (GeneralLinear n R)]

/-- Every Haar measure with inner regularity on this general linear group is right invariant. -/
theorem generalLinear_haar_rightInvariant
    (μ : Measure (GeneralLinear n R)) [μ.IsHaarMeasure] [μ.InnerRegular] :
    μ.IsMulRightInvariant := by
  classical
  let e := generalLinearResidueEquiv R n
  let χ := Measure.modularCharacter.comp e.symm.toMonoidHom
  have hcentral (z : GeneralLinear n R) (hz : z ∈ Subgroup.center (GeneralLinear n R)) :
      Measure.modularCharacter z = 1 := by
    change Measure.modularCharacterFun z = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ z]
    have heq : (· * z) = (z * ·) := funext (Subgroup.mem_center_iff.mp hz)
    have hmap : Measure.map (· * z) μ = μ := by
      rw [heq, map_mul_left_eq_self]
    have hfactor (ν : Measure (GeneralLinear n R)) [ν.IsHaarMeasure] (hν : ν = μ) :
        Measure.haarScalarFactor ν μ = 1 := by
      subst ν
      exact Measure.haarScalarFactor_self _
    exact hfactor _ hmap
  have hχ : χ = 1 := by
    apply MonoidHom.pi_ext
    intro I g
    let _ : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    change (χ.comp (MonoidHom.mulSingle _ I)) g = 1
    apply RankinSelberg.GeneralLinearUnimodularity.character_eq_one
    intro a
    change Measure.modularCharacter
      (e.symm (Pi.mulSingle I (GeneralLinearGroup.scalar (Fin n) a))) = 1
    apply hcentral
    rw [Subgroup.mem_center_iff]
    intro b
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst J
      simpa using (GeneralLinearGroup.scalar_commute a (e b I)).symm
    · simp [Pi.mulSingle_eq_of_ne h]
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  have hg : Measure.modularCharacterFun g = 1 := by
    change Measure.modularCharacter g = 1
    simpa [χ] using DFunLike.congr_fun hχ (e g)
  rw [hg, one_smul]

end Haar

end Langlands.BaseChange
