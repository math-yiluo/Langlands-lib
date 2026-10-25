import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Full central quotients of product groups

The actual central quotient of a product is continuously multiplicatively
isomorphic to the product of the actual central quotients. The construction
works for arbitrary index types, hence in particular for empty finite products.
-/

namespace Langlands.Group.Center

universe uI uG

variable {ι : Type uI} (G : ι → Type uG) [∀ i, Group (G i)]

/-- Membership in the full product center is coordinatewise centrality. -/
theorem mem_center_pi_iff (g : ∀ i, G i) :
    g ∈ Subgroup.center (∀ i, G i) ↔ ∀ i, g i ∈ Subgroup.center (G i) := by
  simp [Subgroup.center_pi, Subgroup.mem_pi]

/-- The coordinate quotient homomorphism before passing to the product center. -/
def quotientPi : (∀ i, G i) →* (∀ i, G i ⧸ Subgroup.center (G i)) where
  toFun g i := QuotientGroup.mk (g i)
  map_one' := by ext i; rfl
  map_mul' g h := by ext i; rfl

@[simp]
theorem quotientPi_apply (g : ∀ i, G i) (i : ι) :
    quotientPi G g i = QuotientGroup.mk (g i) := rfl

/-- The coordinate quotient map kills exactly the full center. -/
theorem ker_quotientPi : (quotientPi G).ker = Subgroup.center (∀ i, G i) := by
  ext g
  simp only [MonoidHom.mem_ker, funext_iff, quotientPi_apply, Pi.one_apply,
    QuotientGroup.eq_one_iff, mem_center_pi_iff]

/-- Representatives can be chosen independently in every coordinate. -/
theorem quotientPi_surjective : Function.Surjective (quotientPi G) := by
  intro q
  choose g hg using fun i => QuotientGroup.mk_surjective (q i)
  exact ⟨g, funext hg⟩

/-- The algebraic equivalence for the quotient by the full product center. -/
noncomputable def quotientPiMulEquiv :
    ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i)) ≃*
      (∀ i, G i ⧸ Subgroup.center (G i)) :=
  QuotientGroup.liftEquiv _ (quotientPi_surjective G) (ker_quotientPi G).symm

@[simp]
theorem quotientPiMulEquiv_mk (g : ∀ i, G i) :
    quotientPiMulEquiv G (QuotientGroup.mk g) = fun i => QuotientGroup.mk (g i) := rfl

@[simp]
theorem quotientPiMulEquiv_symm_mk (g : ∀ i, G i) :
    (quotientPiMulEquiv G).symm (fun i => QuotientGroup.mk (g i)) =
      QuotientGroup.mk g :=
  (quotientPiMulEquiv G).symm_apply_apply (QuotientGroup.mk g)

variable [∀ i, TopologicalSpace (G i)]

/-- The full product center, with its subtype topology, is the product of the
coordinate centers with their subtype topologies. -/
def piCenterContinuousMulEquiv :
    Subgroup.center (∀ i, G i) ≃ₜ* (∀ i, Subgroup.center (G i)) where
  toFun g i := ⟨g.1 i, (mem_center_pi_iff G g.1).mp g.2 i⟩
  invFun z := ⟨fun i => (z i).1, (mem_center_pi_iff G _).mpr fun i => (z i).2⟩
  left_inv g := by ext i; rfl
  right_inv z := by ext i; rfl
  map_mul' g h := by ext i; rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

@[simp]
theorem piCenterContinuousMulEquiv_apply (z : Subgroup.center (∀ i, G i)) (i : ι) :
    (piCenterContinuousMulEquiv G z i : G i) = z.1 i := rfl

@[simp]
theorem piCenterContinuousMulEquiv_symm_apply (z : ∀ i, Subgroup.center (G i)) (i : ι) :
    ((piCenterContinuousMulEquiv G).symm z).1 i = (z i : G i) := rfl

variable [∀ i, IsTopologicalGroup (G i)]

/-- The actual product quotient and product of quotients are continuously
multiplicatively equivalent, using the existing quotient and product topologies. -/
noncomputable def quotientPiContinuousMulEquiv :
    ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i)) ≃ₜ*
      (∀ i, G i ⧸ Subgroup.center (G i)) where
  toMulEquiv := quotientPiMulEquiv G
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (∀ i, G i))).continuous_iff.mpr
    exact continuous_pi fun i => QuotientGroup.continuous_mk.comp (continuous_apply i)
  continuous_invFun := by
    apply (IsOpenQuotientMap.piMap (fun i =>
      (QuotientGroup.isOpenQuotientMap_mk (N := Subgroup.center (G i))))).continuous_comp_iff.mp
    change Continuous (fun g : ∀ i, G i =>
      (quotientPiMulEquiv G).symm (fun i => QuotientGroup.mk (g i)))
    simpa only [quotientPiMulEquiv_symm_mk] using
      (QuotientGroup.continuous_mk (N := Subgroup.center (∀ i, G i)))

@[simp]
theorem quotientPiContinuousMulEquiv_mk (g : ∀ i, G i) :
    quotientPiContinuousMulEquiv G (QuotientGroup.mk g) =
      fun i => QuotientGroup.mk (g i) := rfl

@[simp]
theorem quotientPiContinuousMulEquiv_symm_mk (g : ∀ i, G i) :
    (quotientPiContinuousMulEquiv G).symm (fun i => QuotientGroup.mk (g i)) =
      QuotientGroup.mk g := quotientPiMulEquiv_symm_mk G g

section Borel

variable [MeasurableSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
  [BorelSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
  [MeasurableSpace (∀ i, G i ⧸ Subgroup.center (G i))]
  [BorelSpace (∀ i, G i ⧸ Subgroup.center (G i))]

/-- The quotient identification is measurable for Borel realizations. -/
theorem measurable_quotientPiContinuousMulEquiv :
    Measurable (quotientPiContinuousMulEquiv G) :=
  (quotientPiContinuousMulEquiv G).continuous_toFun.measurable

/-- Its inverse is measurable for Borel realizations. -/
theorem measurable_quotientPiContinuousMulEquiv_symm :
    Measurable (quotientPiContinuousMulEquiv G).symm :=
  (quotientPiContinuousMulEquiv G).continuous_invFun.measurable

/-- The same quotient identification as a measurable equivalence. -/
noncomputable def quotientPiMeasurableEquiv :
    ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i)) ≃ᵐ
      (∀ i, G i ⧸ Subgroup.center (G i)) :=
  (quotientPiContinuousMulEquiv G).toHomeomorph.toMeasurableEquiv

@[simp]
theorem quotientPiMeasurableEquiv_mk (g : ∀ i, G i) :
    quotientPiMeasurableEquiv G (QuotientGroup.mk g) =
      fun i => QuotientGroup.mk (g i) := rfl

@[simp]
theorem quotientPiMeasurableEquiv_symm_mk (g : ∀ i, G i) :
    (quotientPiMeasurableEquiv G).symm (fun i => QuotientGroup.mk (g i)) =
      QuotientGroup.mk g := quotientPiMulEquiv_symm_mk G g

end Borel
end Langlands.Group.Center
