import Langlands.Representation.Hecke.CompactInductionSurjective
import Langlands.Representation.Hecke.CompactTensorInjectivity

/-! The exact compact Hecke tensor comparison of Renard III.2.6. -/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))
  (μH : Measure H) [μH.IsHaarMeasure]

/-- The original component is injective by finite-coset reconstruction. -/
theorem compactComparisonHom_injective (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    Function.Injective (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom :=
  compactComparison_injective_of_pure_values H hH μG μH W.representation W.isSmooth
    (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom (fun _ _ => rfl)

/-- The actual natural isomorphism of Hecke tensor induction and relatively
twisted compact induction. -/
def compactComparisonNatIso :
    tensorInductionHeckeFunctor.{uG, v} μG H μH ≅
      compactModularHeckeFunctor.{uG, v} μG H :=
  compactComparisonNatIsoOfInjective μG H hH μH
    (compactComparisonHom_injective μG H hH μH)

/-- Renard III.2.6, with the exact right action, relative twist, elementary
scalar integral, and all the universes of the published target. -/
theorem compactInductionHeckeStatement_proof : CompactInductionHeckeStatement.{uG, v} := by
  intro G _ _ _ _ _ _ _ μG _ H hH
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  intro μH _
  refine ⟨compactComparisonNatIso μG H hH μH, ?_, ?_⟩
  · exact rightModule_integral μG μH H.subtype continuous_subtype_val
  · exact compactComparisonHom_dual μG H hH μH

end Langlands.Hecke.Homomorphism
