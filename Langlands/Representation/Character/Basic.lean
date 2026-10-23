import Langlands.LinearAlgebra.FiniteRankTrace
import Langlands.Representation.Hecke.FiniteRankAction
import Langlands.HarmonicAnalysis.Distribution.Basic

/-! # The distribution character of an admissible representation -/

noncomputable section

namespace Langlands.Character

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)

/-- The actual integrated action with its finite-rank codomain. -/
def finiteRankIntegratedAction : SchwartzBruhat G →ₗ[ℂ] finiteRankEnd V :=
  (Hecke.integratedAction μ ρ hρ.1).codRestrict (finiteRankEnd V) (fun f =>
    (mem_finiteRankEnd_iff _).mpr (Hecke.integratedAction_finiteDimensional_range μ ρ hρ f))

@[simp]
theorem finiteRankIntegratedAction_coe (f : SchwartzBruhat G) :
    (finiteRankIntegratedAction μ ρ hρ f).val = Hecke.integratedAction μ ρ hρ.1 f := rfl

/-- The character is the genuine finite-rank trace of the integrated action. -/
def distribution : Distribution G :=
  FiniteRankEnd.trace.comp (finiteRankIntegratedAction μ ρ hρ)

@[simp]
theorem distribution_apply (f : SchwartzBruhat G) :
    distribution μ ρ hρ f = FiniteRankEnd.trace (finiteRankIntegratedAction μ ρ hρ f) := rfl

/-- Every finite-dimensional subspace containing the image computes the character. -/
theorem distribution_eq_subspace (f : SchwartzBruhat G) (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (hS : (Hecke.integratedAction μ ρ hρ.1 f).range ≤ S) :
    distribution μ ρ hρ f = LinearMap.trace ℂ S
      (FiniteRankEnd.onSubspace (Hecke.integratedAction μ ρ hρ.1 f) S hS) :=
  FiniteRankEnd.trace_eq_subspace _ S hS

/-- Compute the character on the finite-dimensional fixed vectors of any open
subgroup of left bi-invariance. -/
theorem distribution_eq_fixedVectors (K : OpenSubgroup G) {J : Subgroup G}
    {f : SchwartzBruhat G} (hf : f ∈ Hecke.TestFunction.biInvariant K.toSubgroup J) :
    letI := hρ.2 K
    distribution μ ρ hρ f = LinearMap.trace ℂ (fixedVectors ρ K.toSubgroup)
      ((Hecke.integratedActionToFixed μ ρ hρ.1 hf).comp
        (fixedVectors ρ K.toSubgroup).subtype) := by
  let := hρ.2 K
  exact distribution_eq_subspace μ ρ hρ f (fixedVectors ρ K.toSubgroup)
    (Hecke.integratedAction_range_le_fixedVectors μ ρ hρ.1 hf)

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A genuine equivariant equivalence conjugates the actual finite-rank operators. -/
theorem finiteRankIntegratedAction_equivariant
    (σ : Representation ℂ G W) (hσ : IsAdmissible σ) (E : V ≃ₗ[ℂ] W)
    (hE : ∀ g v, E (ρ g v) = σ g (E v)) (f : SchwartzBruhat G) :
    finiteRankIntegratedAction μ σ hσ f =
      FiniteRankEnd.conjugate E (finiteRankIntegratedAction μ ρ hρ f) := by
  apply Subtype.ext
  ext w
  change Hecke.integratedAction μ σ hσ.1 f w =
    E (Hecke.integratedAction μ ρ hρ.1 f (E.symm w))
  let T := E.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ hE
  simpa only [T, LinearMap.toIntertwiningMap, LinearEquiv.coe_coe,
    E.apply_symm_apply] using
    (Hecke.integratedAction_intertwiner μ hρ.1 hσ.1 T f (E.symm w)).symm

/-- Equivalent admissible representations have equal distribution characters,
with no relation required between their carrier universes. -/
theorem distribution_eq_of_equivariant
    (σ : Representation ℂ G W) (hσ : IsAdmissible σ) (E : V ≃ₗ[ℂ] W)
    (hE : ∀ g v, E (ρ g v) = σ g (E v)) :
    distribution μ ρ hρ = distribution μ σ hσ := by
  ext f
  rw [distribution_apply, distribution_apply,
    finiteRankIntegratedAction_equivariant μ ρ hρ σ hσ E hE,
    FiniteRankEnd.trace_conjugate]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [IsMulLeftInvariant μ] in
/-- Change of variables under an actual inner automorphism. The explicit
measure-preservation assumption is essential for a general left Haar measure. -/
theorem integratedAction_conjugation_of_measurePreserving (a : G)
    (ha : MeasurePreserving (Distribution.conjugationHomeomorph a) μ μ)
    (f : SchwartzBruhat G) (v : V) :
    Hecke.integratedAction μ ρ hρ.1
        (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) v =
      ρ a⁻¹ (Hecke.integratedAction μ ρ hρ.1 f (ρ a v)) := by
  have heq :
      (Hecke.actionIntegrand ρ hρ.1 f (ρ a v)).comp
          (Distribution.conjugationHomeomorph a) ha.measurable =
        (Hecke.actionIntegrand ρ hρ.1
          (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) v).map
          (ρ a) := by
    ext x
    simp [map_mul, Module.End.mul_apply]
  have h := AlgebraicIntegral.integral_comp_measurePreserving
    (Hecke.actionIntegrand ρ hρ.1 f (ρ a v))
    (Distribution.conjugationHomeomorph a) ha
  rw [heq, AlgebraicIntegral.integral_linearMap _
    (Hecke.actionIntegrand_finMeasSupp μ ρ hρ.1
      (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) v) (ρ a)] at h
  exact (ρ.inv_self_apply a _).symm.trans (congrArg (ρ a⁻¹) h)

/-- The character is invariant under each measure-preserving inner automorphism. -/
theorem distribution_conjugation_of_measurePreserving (a : G)
    (ha : MeasurePreserving (Distribution.conjugationHomeomorph a) μ μ)
    (f : SchwartzBruhat G) :
    distribution μ ρ hρ
      (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) =
        distribution μ ρ hρ f := by
  let E : V ≃ₗ[ℂ] V :=
    { ρ a⁻¹ with
      invFun := ρ a
      left_inv := ρ.self_inv_apply a
      right_inv := ρ.inv_self_apply a }
  have he : finiteRankIntegratedAction μ ρ hρ
      (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) =
      FiniteRankEnd.conjugate E (finiteRankIntegratedAction μ ρ hρ f) := by
    apply Subtype.ext
    ext v
    exact integratedAction_conjugation_of_measurePreserving μ ρ hρ a ha f v
  rw [distribution_apply, he, FiniteRankEnd.trace_conjugate, distribution_apply]

/-- Conjugation invariance requires preservation of the chosen measure. -/
theorem distribution_isConjugationInvariant_of_measurePreserving
    (hμ : ∀ a : G, MeasurePreserving (Distribution.conjugationHomeomorph a) μ μ) :
    Distribution.IsConjugationInvariant (distribution μ ρ hρ) := by
  rw [Distribution.isConjugationInvariant_iff]
  exact fun a f => distribution_conjugation_of_measurePreserving μ ρ hρ a (hμ a) f

/-- A left and right invariant measure is preserved by every inner automorphism. -/
theorem distribution_isConjugationInvariant [IsMulRightInvariant μ] :
    Distribution.IsConjugationInvariant (distribution μ ρ hρ) := by
  apply distribution_isConjugationInvariant_of_measurePreserving μ ρ hρ
  intro a
  exact (measurePreserving_mul_right μ a⁻¹).comp (measurePreserving_mul_left μ a)

end Langlands.Character
