import Langlands.HarmonicAnalysis.HomogeneousFunctions
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Smooth induction of the contragredient as a dual (Renard III.2.7, Theorem)

For a closed subgroup `H` of a t.d. group `G` and a smooth representation `(ρ, W)` of `H`,
`Ind_H^G(W̃)` is the smooth dual of `ind_H^G(W ⊗ δ_{H\G})`, the pairing being the integral over
`H \ G` of `h(g)(f(g))` against an invariant functional on the II.3.9 space of
`δ_{H\G}`-covariant functions.
-/

namespace Langlands.Induction

open HarmonicAnalysis.HomogeneousFunctions

universe uG uV

/-- Renard III.2.7, Theorem: let `H` be a closed subgroup of a t.d. group `G`, let `χ` be the
complex character with the values of `δ_{H\G}` and let `ν` be a nonzero right-invariant linear
form on the space of II.3.9 (Renard's `∫_{H\G} … dν_{H\G}`). For every smooth representation
`ρ` of `H` there is an equivalence `Φ : Ind_H^G(ρ̃) ≃ ind_H^G(ρ ⊗ δ_{H\G})~` such that, for
`h ∈ Ind_H^G(ρ̃)` and `f ∈ ind_H^G(ρ ⊗ δ_{H\G})`, the function `g ↦ h(g)(f(g))` lies in that
space and `⟨Φ h, f⟩ = ν(g ↦ h(g)(f(g)))`. -/
def ClosedInductionSmoothDualityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (χ : H →* ℂˣ),
    (∀ h : H, (χ h : ℂ) = ((relativeModular H hH h : ℝ) : ℂ)) →
    ∀ ν : Module.Dual ℂ (renardSpace H hH),
      (∀ (g : G) (φ : renardSpace H hH), ν (rightAction H (relativeModular H hH) g φ) = ν φ) →
      ν ≠ 0 →
      ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W),
        IsSmooth ρ →
        ∃ Φ : (smoothInduced H (smoothContragredient ρ)).Equiv
            (smoothContragredient (compactInduced H (twist χ ρ))),
          ∀ (h : SmoothFunctions H (smoothContragredient ρ))
            (f : CompactFunctions H (twist χ ρ)),
            ∃ φ : renardSpace H hH,
              (∀ g : G, φ.val g =
                smoothDualPairing ρ (eval H _ h g) (eval H _ f.val g)) ∧
              smoothDualPairing _ (Φ h) f = ν φ

end Langlands.Induction
