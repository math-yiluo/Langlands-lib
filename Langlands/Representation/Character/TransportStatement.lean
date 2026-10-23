import Langlands.Representation.Character.Basic
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Character transport under smooth duality and group automorphisms -/

namespace Langlands

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

/-- The actual smooth dual has the character obtained by inverting test functions. -/
def CharacterSmoothDualStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
    [IsInvInvariant μ]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ),
    ∃ hdual : IsAdmissible (smoothContragredient ρ),
      ∀ f : SchwartzBruhat G,
        Character.distribution μ (smoothContragredient ρ) hdual f =
          Character.distribution μ ρ hρ (Hecke.TestFunction.inversion f)

/-- Pulling back an actual representation pulls back its character test functions
by the inverse automorphism, when the chosen measure is preserved. -/
def CharacterAutomorphismStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
    (e : G ≃ₜ* G), MeasurePreserving e μ μ →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ),
      ∃ hpull : IsAdmissible (ρ.comp e.toMonoidHom),
        ∀ f : SchwartzBruhat G,
          Character.distribution μ (ρ.comp e.toMonoidHom) hpull f =
            Character.distribution μ ρ hρ
              (Hecke.TestFunction.pullback e.symm.toHomeomorph f)

/-- The two character transport identities used in the contragredient argument. -/
def CharacterTransportStatement : Prop :=
  CharacterSmoothDualStatement.{uG,uV} ∧ CharacterAutomorphismStatement.{uG,uV}

end Langlands
