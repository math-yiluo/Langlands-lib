import Langlands.Representation.Character.Basic
import Langlands.Representation.Twist.Definitions

/-! # Character weights on Schwartz–Bruhat tests -/

noncomputable section

namespace Langlands.Character

open HarmonicAnalysis MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The test function `g ↦ χ(g) f(g)` for a locally constant character `χ`. -/
def weightedTest (χ : G →* ℂˣ)
    (hloc : IsLocallyConstant fun g : G => (χ g : ℂ)) (f : SchwartzBruhat G) :
    SchwartzBruhat G :=
  ⟨fun g => (χ g : ℂ) * f g, hloc.comp₂ f.locallyConstant (· * ·), f.hasCompactSupport.mul_left⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in
@[simp]
theorem weightedTest_apply (χ : G →* ℂˣ)
    (hloc : IsLocallyConstant fun g : G => (χ g : ℂ)) (f : SchwartzBruhat G) (g : G) :
    weightedTest χ hloc f g = (χ g : ℂ) * f g := rfl

/-- The character of a twist `χ ⊗ ρ` at `f` is the character of `ρ` at `χ f`. -/
theorem distribution_twist_weightedTest (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (χ : G →* ℂˣ)
    (hloc : IsLocallyConstant fun g : G => (χ g : ℂ))
    (htwist : IsAdmissible (twist χ ρ)) (f : SchwartzBruhat G) :
    Character.distribution μ (twist χ ρ) htwist f =
      Character.distribution μ ρ hρ (weightedTest χ hloc f) := by
  rw [Character.distribution_apply, Character.distribution_apply]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  simp only [Character.finiteRankIntegratedAction_coe]
  ext x
  rw [Hecke.integratedAction_apply, Hecke.integratedAction_apply]
  congr 1
  ext g
  simp only [Hecke.actionIntegrand_apply]
  change f g • ((χ g : ℂ) • ρ g x) = ((χ g : ℂ) * f g) • ρ g x
  rw [smul_smul, mul_comm (f g) (χ g : ℂ)]

/-- Equivalent admissible representations have the same character. -/
theorem distribution_eq_of_equiv (μ : Measure G) [μ.IsHaarMeasure]
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (hρ : IsAdmissible ρ) (hρ' : IsAdmissible ρ') (e : ρ.Equiv ρ') :
    Character.distribution μ ρ hρ = Character.distribution μ ρ' hρ' :=
  Character.distribution_eq_of_equivariant μ ρ hρ ρ' hρ' e.toLinearEquiv
    (fun g x => DFunLike.congr_fun (e.isIntertwining' g) x)

end Langlands.Character
