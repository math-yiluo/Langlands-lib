import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.Geometric.CosetOrbitOrdering

/-!
# All-field port of `Langlands.Representation.Geometric.CosetOrbitOrdering`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.CosetOrbitOrdering` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
universe uG

variable {G : Type uG} [Group G] (P Q : Subgroup G)

attribute [local instance] leftQuotientAction

/-- The general finite orbit ordering implies the closed-subgroup specialization. -/
theorem closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
    (h : Langlands.Topology.FiniteOrbitOrdering.{uG, uG}) :
    ClosedSubgroupOrbitOrdering.{uG} := by
  intro G _ _ _ _ _ _ P Q hP hQ hfinite
  let : MulAction Q (Induction.LeftQuotient P) := leftQuotientAction P Q
  let : ContinuousSMul Q (Induction.LeftQuotient P) :=
    leftQuotientAction_continuousSMul P Q
  let : T2Space (Induction.LeftQuotient P) :=
    QuotientIntegration.leftQuotient_t2Space P hP
  let : LocallyCompactSpace (Induction.LeftQuotient P) :=
    QuotientIntegration.leftQuotient_locallyCompactSpace P
  let : SigmaCompactSpace Q := hQ.sigmaCompactSpace
  let := hfinite
  obtain ⟨n, r, hcover, hdisjoint, hopen⟩ := h Q (Induction.LeftQuotient P)
    (finite_leftQuotientAction_orbits P Q)
  choose g hg using fun i => Quotient.exists_rep (r i)
  have horbit (i : Fin n) : MulAction.orbit Q (r i) = cosetOrbit P Q (g i)⁻¹ := by
    calc
      MulAction.orbit Q (r i) = MulAction.orbit Q (Induction.quotientMap P (g i)) :=
        congrArg (MulAction.orbit Q) (hg i).symm
      _ = cosetOrbit P Q (g i)⁻¹ := by
        simpa only [inv_inv] using leftQuotientAction_orbit P Q (g i)⁻¹
  refine ⟨n, ⟨{ representative := fun i => (g i)⁻¹
                covers := ?_
                disjoint := ?_
                initial_open := ?_ }⟩⟩
  · simpa only [horbit] using hcover
  · simpa only [horbit] using hdisjoint
  · simpa only [horbit] using hopen

end Langlands.AllFieldBZ.Geometric
