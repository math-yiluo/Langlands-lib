import Langlands.Representation.Geometric.CosetAction
import Langlands.Representation.Geometric.OrbitRepresentatives
import Langlands.Representation.Geometric.ClosedSubgroupStatement
import Langlands.Topology.GroupAction.FiniteOrbitStatement

/-! Relating actual double cosets to the inverse right action orbit quotient. -/

noncomputable section

namespace Langlands.Geometric

universe uG

variable {G : Type uG} [Group G] (P Q : Subgroup G)

attribute [local instance] leftQuotientAction

/-- Equality in the actual action orbit quotient is equality of double cosets. -/
theorem leftQuotientAction_orbitRel_iff (g h : G) :
    MulAction.orbitRel Q (Induction.LeftQuotient P)
      (Induction.quotientMap P g) (Induction.quotientMap P h) ↔
      DoubleCoset.mk P Q g = DoubleCoset.mk P Q h := by
  rw [MulAction.orbitRel_apply]
  have horbit : MulAction.orbit Q (Induction.quotientMap P h) = cosetOrbit P Q h⁻¹ := by
    simpa only [inv_inv] using leftQuotientAction_orbit P Q h⁻¹
  rw [horbit, quotientMap_mem_cosetOrbit_iff, inv_inv, eq_comm]

/-- The double-coset quotient is the orbit quotient of inverse right translation. -/
def doubleCosetEquivOrbitQuotient :
    DoubleCoset.Quotient (P : Set G) (Q : Set G) ≃
      MulAction.orbitRel.Quotient Q (Induction.LeftQuotient P) := by
  let f : DoubleCoset.Quotient (P : Set G) (Q : Set G) →
      MulAction.orbitRel.Quotient Q (Induction.LeftQuotient P) :=
    Quotient.lift (fun g => Quotient.mk'' (Induction.quotientMap P g)) (by
      intro g h hgh
      apply Quotient.sound
      exact (leftQuotientAction_orbitRel_iff P Q g h).mpr (Quotient.sound hgh))
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        exact (leftQuotientAction_orbitRel_iff P Q a b).mp (Quotient.exact hab)
  · intro x
    induction x using Quotient.inductionOn with
    | h x =>
      induction x using Quotient.inductionOn with
      | h x => exact ⟨DoubleCoset.mk P Q x, rfl⟩

@[simp] theorem doubleCosetEquivOrbitQuotient_mk (g : G) :
    doubleCosetEquivOrbitQuotient P Q (DoubleCoset.mk P Q g) =
      Quotient.mk'' (Induction.quotientMap P g) := rfl

/-- Finiteness of double cosets supplies the actual action orbit quotient hypothesis. -/
theorem finite_leftQuotientAction_orbits
    [Finite (DoubleCoset.Quotient (P : Set G) (Q : Set G))] :
    Finite (MulAction.orbitRel.Quotient Q (Induction.LeftQuotient P)) :=
  Finite.of_surjective _ (doubleCosetEquivOrbitQuotient P Q).surjective

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

end Langlands.Geometric
