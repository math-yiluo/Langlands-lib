import Langlands.VirtualRepresentation.Weil.ExactCoefficients
import Langlands.VirtualRepresentation.Weil.ExactRealizationStatement

/-!
# Exact K0 realization is bijective

The Jordan–Hölder coefficient map is a two-sided inverse of the canonical
exact realization.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation ExactCoefficients

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- The realization of a composition-series sum is the actual exact class. -/
theorem realizeExact_seriesSum (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors) :
    realizeExact G (seriesSum A s hs) = ExactGrothendieckGroup.ofRepresentation _ A := by
  rw [seriesSum, map_sum, exactClass_eq_sum_of_filtration A s]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact realizeExact_ofRepresentation _ _ (hs i) _ rfl

/-- The coefficient map is a right inverse of the canonical realization. -/
theorem realizeExact_comp_exactCoefficients :
    (realizeExact.{uG, uV} G).comp (exactCoefficients.{uG, uV} G) = LinearMap.id := by
  apply ExactGrothendieckGroup.hom_ext
  intro c
  rw [LinearMap.comp_apply, exactCoefficients, ExactGrothendieckGroup.lift_ofClass]
  induction c using Quotient.inductionOn with
  | h A =>
    change realizeExact G (coefficients A) = ExactGrothendieckGroup.ofRepresentation _ A
    exact realizeExact_seriesSum G A _ _

/-- The canonical exact realization is surjective. -/
theorem realizeExact_surjective : Function.Surjective (realizeExact.{uG, uV} G) :=
  fun x => ⟨exactCoefficients G x, LinearMap.congr_fun (realizeExact_comp_exactCoefficients G) x⟩

/-- **Exact K0 realization.** The canonical integral realization of genuine
continuous irreducible classes into the exact quotient is bijective. -/
theorem exactRealizationBijective : ExactRealizationBijectiveStatement.{uG, uV} G :=
  ⟨realizeExact_injective G, realizeExact_surjective G⟩

/-- Every exact virtual class has a unique integral irreducible expansion. -/
theorem exactExpansionUnique : ExactExpansionUniqueStatement.{uG, uV} G :=
  (exactRealizationBijective_iff_uniqueExpansion G).mp (exactRealizationBijective G)

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uF uW

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Exact K0 realization for the actual local Weil group. -/
theorem exactRealizationBijective : ExactRealizationBijectiveStatement.{uF, uW} F :=
  Weil.exactRealizationBijective (localWeilGroup F)

/-- Unique exact expansion for the actual local Weil group. -/
theorem exactExpansionUnique : ExactExpansionUniqueStatement.{uF, uW} F :=
  (exactRealizationBijective_iff_uniqueExpansion F).mp (exactRealizationBijective F)

end Langlands.VirtualRepresentation.LocalWeil
