import Langlands.HarmonicAnalysis.Distribution.CharacterAverage

/-!
# Unique factorization of twisted product distributions

The distribution part of Shalika (1974), Proposition 1.12, for a nonarchimedean
group `G` and an arbitrary locally compact, Hausdorff, totally disconnected `Y`.
An algebraic distribution on `G × (Y × G)` that transforms by `χ` under left
translation of the first factor and right translation of the last factor is the
algebraic dual of the character average of exactly one distribution on `Y`.
This module defines an unproved proposition; see the paired Markdown.
-/

namespace Langlands.HarmonicAnalysis.Distribution

open MeasureTheory

universe uG uY

/-- For every Hausdorff, locally compact, nonarchimedean group `G` with its Borel
structure, every Hausdorff, locally compact, totally disconnected space `Y`, every
continuous character `χ : G → ℂˣ` and every left Haar measure `μ` on `G` that is
s-finite and right invariant, each algebraic distribution `D` on `G × (Y × G)` with
`D (α ∘ e) = (χ a * χ b) * D α` for `e (g₁, (y, g₂)) = (a * g₁, (y, g₂ * b))`
equals `characterAverageDual χ μ τ` for exactly one algebraic distribution `τ` on `Y`. -/
def CharacterAverageFactorizationStatement : Prop :=
  ∀ (G : Type uG) (Y : Type uY) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    [μ.IsMulRightInvariant] (D : Distribution (G × (Y × G))),
    (∀ (a b : G) (α : SchwartzBruhat (G × (Y × G))),
      D (Hecke.TestFunction.pullback
          ((Homeomorph.mulLeft a).prodCongr
            ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b))) α) =
        ((χ a : ℂ) * (χ b : ℂ)) * D α) →
    ∃! τ : Distribution Y, Distribution.characterAverageDual χ μ τ = D

end Langlands.HarmonicAnalysis.Distribution
