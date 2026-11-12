import Langlands.Representation.Hecke.HomomorphismSmooth
import Langlands.Algebra.NondegenerateInductionAdjunctionStatements

/-! # Continuous-homomorphism restriction and induction: proposition targets

Renard III.2.1, printed p.70 / PDF p.76, applying I.2.3.
These are closed propositions, not assumed instances or asserted proofs.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra

universe uG uH v

/-- III.2.1 and I.2.3: the actual Hecke functors satisfy both canonical
adjunctions, including the original tensor evaluation formulas and naturality.
The carrier universe is stable under the actual tensor/Hom constructions. -/
def HeckeInductionAdjunctionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Type uH) [Group H] [TopologicalSpace H] [T2Space H]
    [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
    (φ : H →* G) (hφ : Continuous φ),
    (letI := leftModule μG μH φ hφ
     letI := NonUnitalModule.rightRegular (HeckeAlgebra μG)
     NondegenerateInductionAdjunction.CanonicalFInductionAdjunction.{uH, uG, v}
       (isIdempotented μH) (isIdempotented μG)
       (left_commutes_regular μG μH φ hφ) (left_regular_nondegenerate μG μH φ hφ)) ∧
    (letI := NonUnitalModule.regular (HeckeAlgebra μG)
     letI := rightModule μG μH φ hφ
     NondegenerateInductionAdjunction.CanonicalPInductionAdjunction.{uH, uG, v}
       (isIdempotented μH) (isIdempotented μG)
       (regular_commutes_right μG μH φ hφ) (regular_right_nondegenerate μG μH φ hφ))

/-- III.2.1: the specific Hecke functors of III.1.4 are equivalences;
under their transport, `Fφ` is naturally isomorphic to the tensor `F`,
`F` is left adjoint to `I`, and `P` is left adjoint to pseudo-`F`.
The equivalences and adjunctions are conclusions, not supplied hypotheses. -/
def SmoothInductionAdjunctionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Type uH) [Group H] [TopologicalSpace H] [T2Space H]
    [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
    (φ : H →* G) (hφ : Continuous φ),
    ∃ eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence,
    ∃ eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence,
      Nonempty (restriction.{uG, uH, max uG v} φ hφ ≅ smoothF μG μH φ hφ eH) ∧
      Nonempty (smoothF μG μH φ hφ eH ⊣ smoothI μG μH φ hφ eG) ∧
      Nonempty (smoothP μG μH φ hφ eG ⊣ smoothPseudoF μG μH φ hφ eH)

/-- The continuous-homomorphism comparison and both induction adjunctions
in Renard III.2.1 (printed p.70 / PDF p.76). -/
def ContinuousHomomorphismStatements : Prop :=
  HeckeInductionAdjunctionStatement.{uG, uH, v} ∧
    SmoothInductionAdjunctionStatement.{uG, uH, v}

end Langlands.Hecke.Homomorphism
