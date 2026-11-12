import Langlands.Representation.Hecke.CompactInductionModels

/-! # The compact Hecke-induction comparison

Renard III.2.6, (III.2.6.1)–(III.2.6.2) and Theorem,
printed pp.75–76 / PDF pp.81–82.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

universe uG v

section Evaluation

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H]

/-- Evaluation in the actual relatively twisted compact-function model. -/
def compactModularEvaluation (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : ((compactModularHeckeFunctor μG H).obj W).obj) (g : G) : W :=
  Induction.eval H
    (Langlands.twist
      (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom
      W.representation)
    (show Induction.CompactFunctions H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom
        W.representation) from f).val g

end Evaluation

/-- Renard III.2.6 Theorem: `P(W)` is naturally isomorphic, by the prescribed
integral map `p`, to compact induction of `W ⊗ δ_{H\G}`.
The right action is exactly (III.2.6.1), and the map on elementary tensors
is specified by every complex-linear functional, without topologizing `W`. -/
def CompactInductionHeckeStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    letI : LocallyCompactSpace H := hH.locallyCompactSpace
    ∀ (μH : Measure H) [μH.IsHaarMeasure],
    letI := rightModule μG μH H.subtype continuous_subtype_val
    ∃ p : tensorInductionHeckeFunctor.{uG, v} μG H μH ≅
        compactModularHeckeFunctor.{uG, v} μG H,
      (∀ (a : HeckeAlgebra μH) (T : HeckeAlgebra μG) (x : G),
        (op a • T) x =
          ∫ h : H, haarScale (h : G) * a h * T (x * (h : G)⁻¹) ∂μH) ∧
      (∀ (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
          (T : HeckeAlgebra μG) (w : W) (g : G) (ell : W →ₗ[ℂ] ℂ),
        ell (compactModularEvaluation μG H W
          ((p.hom.app W).hom.toAddMonoidHom (tensorInductionTmul μG H μH W T w)) g) =
            ∫ h : H, T (((h : G) * g)⁻¹) * haarScale (h : G) *
              ell (W.representation h⁻¹ w) ∂μH)

end Langlands.Hecke.Homomorphism
