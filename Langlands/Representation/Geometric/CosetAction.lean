import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.SigmaCompact

/-! The actual inverse right action on left cosets and its orbit quotient. -/

namespace Langlands.Geometric

universe uG

variable {G : Type uG} [Group G] (P Q : Subgroup G)

/-- The left action of `Q` on `P \ G` by inverse right translation. -/
@[instance_reducible]
def leftQuotientAction : MulAction Q (Induction.LeftQuotient P) where
  smul q x := Induction.quotientRight P (q : G)⁻¹ x
  one_smul x := by
    induction x using Quotient.inductionOn with
    | h x => change Induction.quotientMap P (x * (1 : G)⁻¹) = _; simp
  mul_smul q r x := by
    induction x using Quotient.inductionOn with
    | h x =>
      change Induction.quotientMap P (x * ((q : G) * (r : G))⁻¹) =
        Induction.quotientMap P ((x * (r : G)⁻¹) * (q : G)⁻¹)
      simp only [mul_inv_rev, mul_assoc]

attribute [local instance] leftQuotientAction

@[simp] theorem leftQuotientAction_smul_mk (q : Q) (g : G) :
    q • Induction.quotientMap P g = Induction.quotientMap P (g * (q : G)⁻¹) := rfl

/-- The inverse-right-action orbit is exactly the published orbit convention. -/
theorem leftQuotientAction_orbit (w : G) :
    MulAction.orbit Q (Induction.quotientMap P w⁻¹) = cosetOrbit P Q w := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q⁻¹, rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨q⁻¹, ?_⟩
    change Induction.quotientMap P (w⁻¹ * ((q⁻¹ : Q) : G)⁻¹) = _
    simp only [InvMemClass.coe_inv, inv_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The quotient action is jointly continuous. -/
theorem leftQuotientAction_continuousSMul :
    ContinuousSMul Q (Induction.LeftQuotient P) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (QuotientIntegration.leftQuotient_isOpenQuotientMap P)).continuous_comp_iff]
    exact continuous_quotient_mk'.comp
      (continuous_snd.mul (continuous_subtype_val.comp continuous_fst).inv)

end Langlands.Geometric
