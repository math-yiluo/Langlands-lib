import Langlands.Representation.Hecke.MackeyModels

/-! # Renard's two Mackey natural isomorphisms

Renard III.2.11 Theorem, printed pp.82–83 / PDF pp.88–89.
The tensor identity retains the pseudo-forgetful/forgetful comparison hypothesis.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Hecke.Homomorphism

universe uG uH v

/-- III.2.11 Theorem: smooth Hom commutes with right Hecke induction; tensor
commutes with left Hecke induction provided pseudo-forgetting is naturally
isomorphic to forgetting. Each isomorphism is natural in both representations.
Equivalence of the exact Hecke functors and `Fφ ≅ F` are conclusions. -/
def MackeyIsomorphismStatements : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Type uH) [Group H] [TopologicalSpace H] [T2Space H]
    [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
    (φ : H →* G) (hφ : Continuous φ),
    ∃ eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence,
    ∃ eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence,
      Nonempty (restriction.{uG, uH, max uG v} φ hφ ≅ smoothF μG μH φ hφ eH) ∧
      Nonempty (mackeyHomLeft μG μH φ hφ eG ≅ mackeyHomRight μG μH φ hφ eG) ∧
      (Nonempty (smoothPseudoF μG μH φ hφ eH ≅ smoothF μG μH φ hφ eH) →
        Nonempty (mackeyTensorLeft μG μH φ hφ eG ≅ mackeyTensorRight μG μH φ hφ eG))

end Langlands.Hecke.Homomorphism
