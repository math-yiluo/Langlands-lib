import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.NormalSubgroupHaarModulus

/-!
# Haar measure on a product group modulo a product subgroup

The quotient of a product by a product of normal subgroups is isomorphic as a
topological group to the product of the factor quotients. For finitely many
factors, this identifies a Haar measure on the actual quotient from the supplied
Haar measures on the factors.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

universe uι uG

variable {ι : Type uι} {G : ι → Type uG} [∀ i, Group (G i)]
  (Z : ∀ i, Subgroup (G i))

instance piSubgroupNormal [∀ i, (Z i).Normal] : (Subgroup.pi Set.univ Z).Normal where
  conj_mem x hx y i hi := Subgroup.Normal.conj_mem inferInstance (x i) (hx i hi) (y i)

/-- The product of central subgroups is central in the product group. -/
theorem piSubgroup_le_center (hZ : ∀ i, Z i ≤ Subgroup.center (G i)) :
    Subgroup.pi Set.univ Z ≤ Subgroup.center (∀ i, G i) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  funext i
  exact Subgroup.mem_center_iff.mp (hZ i (hx i (Set.mem_univ i))) (y i)

variable [∀ i, TopologicalSpace (G i)]

/-- The product of closed subgroups is closed in the product group. -/
theorem isClosed_piSubgroup (hZ : ∀ i, IsClosed (Z i : Set (G i))) :
    IsClosed (Subgroup.pi Set.univ Z : Set (∀ i, G i)) :=
  isClosed_set_pi fun i _ => hZ i

variable [∀ i, IsTopologicalGroup (G i)] [∀ i, (Z i).Normal]

/-- The quotient of a product by the product subgroup is the product of the
actual quotient groups. -/
def quotientGroupPiEquiv :
    ((∀ i, G i) ⧸ Subgroup.pi Set.univ Z) ≃ₜ* (∀ i, G i ⧸ Z i) := by
  let e := (normalLeftQuotientHomeomorph (Subgroup.pi Set.univ Z)).symm.trans
    ((leftQuotientPiHomeomorph Z).trans
      (Homeomorph.piCongrRight fun i => normalLeftQuotientHomeomorph (Z i)))
  exact
    { toMulEquiv :=
        { e.toEquiv with
          map_mul' := fun a b => QuotientGroup.induction_on a fun x =>
            QuotientGroup.induction_on b fun y => rfl }
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }

/-- The equivalence sends a representative to the family of its component classes. -/
@[simp]
theorem quotientGroupPiEquiv_mk (x : ∀ i, G i) :
    quotientGroupPiEquiv Z (x : (∀ i, G i) ⧸ Subgroup.pi Set.univ Z) =
      fun i => (x i : G i ⧸ Z i) := rfl

variable [Fintype ι] [∀ i, MeasurableSpace (G i ⧸ Z i)]
  [∀ i, BorelSpace (G i ⧸ Z i)] [∀ i, SecondCountableTopology (G i ⧸ Z i)]
  [MeasurableSpace ((∀ i, G i) ⧸ Subgroup.pi Set.univ Z)]
  [BorelSpace ((∀ i, G i) ⧸ Subgroup.pi Set.univ Z)]
  (μ : ∀ i, Measure (G i ⧸ Z i))

/-- Transport the finite product of the supplied measures to the actual quotient. -/
def quotientGroupPiMeasure : Measure ((∀ i, G i) ⧸ Subgroup.pi Set.univ Z) :=
  Measure.map (quotientGroupPiEquiv Z).symm (Measure.pi μ)

instance [∀ i, SigmaFinite (μ i)] [∀ i, IsHaarMeasure (μ i)] :
    IsHaarMeasure (quotientGroupPiMeasure Z μ) :=
  (quotientGroupPiEquiv Z).symm.isHaarMeasure_map (Measure.pi μ)

/-- A quotient rectangle has volume equal to the product of the factor volumes. -/
theorem quotientGroupPiMeasure_rectangle [∀ i, SigmaFinite (μ i)]
    (s : ∀ i, Set (G i ⧸ Z i)) :
    quotientGroupPiMeasure Z μ ((quotientGroupPiEquiv Z) ⁻¹' (Set.univ.pi s)) =
      ∏ i, μ i (s i) := by
  let e := (quotientGroupPiEquiv Z).toHomeomorph.toMeasurableEquiv
  change (Measure.map e.symm (Measure.pi μ)) (e ⁻¹' (Set.univ.pi s)) = _
  rw [e.symm.map_apply, ← Set.preimage_comp, e.self_comp_symm, Set.preimage_id]
  exact Measure.pi_pi μ s

/-- Integration on the quotient is integration against the supplied finite product. -/
theorem integral_quotientGroupPiMeasure {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : ((∀ i, G i) ⧸ Subgroup.pi Set.univ Z) → V) :
    ∫ q, f q ∂quotientGroupPiMeasure Z μ =
      ∫ q, f ((quotientGroupPiEquiv Z).symm q) ∂Measure.pi μ :=
  integral_map_equiv (quotientGroupPiEquiv Z).symm.toHomeomorph.toMeasurableEquiv f

end Langlands.QuotientIntegration
