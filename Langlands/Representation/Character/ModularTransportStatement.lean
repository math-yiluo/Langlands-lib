import Langlands.Representation.Character.TransportStatement
import Langlands.HarmonicAnalysis.Distribution.Haar

/-!
# Characters under conjugation and duality for non-unimodular groups (Renard III.1.12)

For an admissible representation of a t.d. group and a left Haar measure, conjugating a test
function by `g₀` multiplies the character by `δ_G(g₀)`, and the character of the
contragredient is `Θ_π̃(f) = Θ_π(f̌ δ_G⁻¹)`. Here `δ_G` is Renard's modular character.
-/

namespace Langlands

open HarmonicAnalysis MeasureTheory

universe uG uV

/-- Renard III.1.12, Lemma: for an admissible representation `ρ` of a t.d. group `G`, a left
Haar measure `μ`, `g₀ ∈ G` and a test function `f`, the test function
`x ↦ f(g₀ x g₀⁻¹)` has character value `δ_G(g₀) Θ_ρ(f)`. -/
def CharacterConjugationModularStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (g₀ : G) (f : SchwartzBruhat G),
    ∃ h : SchwartzBruhat G, (∀ x : G, h x = f (g₀ * x * g₀⁻¹)) ∧
      Character.distribution μ ρ hρ h =
        ((Distribution.renardModular g₀ : ℝ) : ℂ) * Character.distribution μ ρ hρ f

/-- Renard III.1.12, Example: for an admissible representation `ρ` of a t.d. group `G` and a
left Haar measure `μ`, the smooth contragredient is admissible and its character is
`Θ_ρ̃(f) = Θ_ρ(f̌ δ_G⁻¹)`, where `(f̌ δ_G⁻¹)(g) = f(g⁻¹) δ_G(g)⁻¹`. -/
def CharacterContragredientModularStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ),
    ∃ hdual : IsAdmissible (smoothContragredient ρ),
      ∀ f : SchwartzBruhat G, ∃ h : SchwartzBruhat G,
        (∀ g : G, h g = f g⁻¹ * (((Distribution.renardModular g : ℝ)⁻¹ : ℝ) : ℂ)) ∧
        Character.distribution μ (smoothContragredient ρ) hdual f =
          Character.distribution μ ρ hρ h

end Langlands
