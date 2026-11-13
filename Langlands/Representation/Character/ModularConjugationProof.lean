import Langlands.Representation.Character.ModularTransportStatement
import Langlands.HarmonicAnalysis.Distribution.RenardModularProof
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace Langlands.Character

open HarmonicAnalysis MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A scalar coefficient of an actual action integrand is a test function. -/
def scalarActionTest (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) (L : Module.Dual ℂ V) : SchwartzBruhat G :=
  ⟨fun x => f x * L (ρ x v),
    f.locallyConstant.mul ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp L),
    f.hasCompactSupport.mul_right⟩

@[simp]
theorem scalarActionTest_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) (L : Module.Dual ℂ V) (x : G) :
    scalarActionTest ρ hρ f v L x = f x * L (ρ x v) := rfl

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)

/-- Conjugation of the actual integrated operator includes Renard's modular factor. -/
theorem integratedAction_conjugation_modular (a : G) (f : SchwartzBruhat G) (v : V) :
    Hecke.integratedAction μ ρ hρ.1
        (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) v =
      ((Distribution.renardModular a : ℝ) : ℂ) •
        ρ a⁻¹ (Hecke.integratedAction μ ρ hρ.1 f (ρ a v)) := by
  apply Module.eval_apply_injective ℂ
  apply LinearMap.ext
  intro L
  change L (Hecke.integratedAction μ ρ hρ.1
      (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) v) = _
  rw [map_smul]
  change L (Hecke.integratedAction μ ρ hρ.1
      (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) v) =
    ((Distribution.renardModular a : ℝ) : ℂ) *
      (L.comp (ρ a⁻¹)) (Hecke.integratedAction μ ρ hρ.1 f (ρ a v))
  rw [Hecke.integratedAction_dual, Hecke.integratedAction_dual]
  have ht := (Distribution.RenardModular.translation G μ).2
    (scalarActionTest ρ hρ.1 f (ρ a v) (L.comp (ρ a⁻¹))) a a
  simpa [scalarActionTest_apply, Distribution.ofMeasure_apply, map_mul,
    Module.End.mul_apply] using ht

/-- Taking the genuine finite-rank trace gives the modular character formula. -/
theorem distribution_conjugation_modular (a : G) (f : SchwartzBruhat G) :
    distribution μ ρ hρ
        (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) =
      ((Distribution.renardModular a : ℝ) : ℂ) * distribution μ ρ hρ f := by
  let E : V ≃ₗ[ℂ] V :=
    { ρ a⁻¹ with
      invFun := ρ a
      left_inv := ρ.self_inv_apply a
      right_inv := ρ.inv_self_apply a }
  have he : finiteRankIntegratedAction μ ρ hρ
      (Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a) f) =
      ((Distribution.renardModular a : ℝ) : ℂ) •
        FiniteRankEnd.conjugate E (finiteRankIntegratedAction μ ρ hρ f) := by
    apply Subtype.ext
    ext v
    exact integratedAction_conjugation_modular μ ρ hρ a f v
  rw [distribution_apply, he, map_smul, FiniteRankEnd.trace_conjugate]
  rfl

end Langlands.Character

namespace Langlands

universe uG uV

/-- Renard III.1.12 Lemma, for every left Haar measure at the published universes. -/
theorem characterConjugationModular : CharacterConjugationModularStatement.{uG,uV} := by
  intro G _ _ _ _ _ _ _ _ μ _ V _ _ ρ hρ a f
  refine ⟨Hecke.TestFunction.pullback
    (HarmonicAnalysis.Distribution.conjugationHomeomorph a) f, ?_, ?_⟩
  · intro x
    rfl
  · exact Character.distribution_conjugation_modular μ ρ hρ a f

end Langlands
