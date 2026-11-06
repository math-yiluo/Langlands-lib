import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Mathlib.FieldTheory.Galois.Abelian

/-! # Unramified norm groups below overgroups of integral units -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open Langlands.LocalClassField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

/-- Every finite-index overgroup of integral units contains a finite unramified
abelian norm group with degree equal to the subgroup index. -/
def UnramifiedNormSubgroupContainment (F : PadicField.{u} p)
    (H : Subgroup F.Carrierˣ) : Prop :=
  H.FiniteIndex → F.canonicalTopologicalData.unitSubgroup ≤ H →
    ∃ E : FiniteIntermediateExtension F.Carrier,
      IsAbelianGalois F.Carrier E.field ∧
      F.canonicalTopologicalData.ramificationIndex =
        (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
      Module.finrank F.Carrier E.field = H.index ∧
      normSubgroup F.Carrier E.field ≤ H

/-- In any subgroup containing all integral units, divisibility of normalized
order by the subgroup index is sufficient for membership. -/
theorem mem_subgroup_of_index_dvd_ord
    (T : F.TopologicalData) (H : Subgroup F.Carrierˣ)
    (hU : T.unitSubgroup ≤ H) (a : F.Carrierˣ)
    (ha : (H.index : ℤ) ∣ T.ord (a : F.Carrier)) : a ∈ H := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨x, hx, hxord⟩ := T.ord_surjective_nonzero k
  let b : F.Carrierˣ := Units.mk0 x hx
  have hb : T.ord (b : F.Carrier) = k := hxord
  have hc : T.ord ((b ^ H.index : F.Carrierˣ) : F.Carrier) =
      (H.index : ℤ) * k := by
    change T.ord ((b : F.Carrier) ^ H.index) = _
    rw [← zpow_natCast, T.ord_zpow, hb]
  have hratio : T.ord ((a / b ^ H.index : F.Carrierˣ) : F.Carrier) = 0 := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv,
      T.ord_mul a.ne_zero (inv_ne_zero (b ^ H.index).ne_zero), T.ord_inv, hk, hc]
    exact add_neg_cancel _
  have hratioH : a / b ^ H.index ∈ H := by
    apply hU
    rw [← T.unitFiltration_zero]
    exact T.mem_unitFiltration_zero_of_ord_eq_zero _ hratio
  simpa using H.mul_mem hratioH (H.pow_index_mem b)

/-- Every finite-index overgroup of the integral units contains the actual
norm group of a finite unramified abelian intermediate extension. -/
theorem exists_unramified_normSubgroup_le
    (F : PadicField.{u} p) (H : Subgroup F.Carrierˣ) [H.FiniteIndex]
    (hU : F.canonicalTopologicalData.unitSubgroup ≤ H) :
    ∃ E : FiniteIntermediateExtension F.Carrier,
      IsAbelianGalois F.Carrier E.field ∧
      F.canonicalTopologicalData.ramificationIndex =
        (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
      Module.finrank F.Carrier E.field = H.index ∧
      normSubgroup F.Carrier E.field ≤ H := by
  obtain ⟨E, hG, he, hdegree⟩ :=
    unramifiedExtensionDegreeExistence p F H.index
      (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H)))
  let : IsGalois F.Carrier E.field := hG
  let := (E.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier (E.asPadicField (p := p)).Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨χ, _⟩ := arithmeticUnramifiedCoordinateExistence
    p F (E.asPadicField (p := p)) he
  let : IsCyclic Gal(E.field/F.Carrier) :=
    isCyclic_of_injective χ.toMonoidHom χ.injective
  have hab : IsAbelianGalois F.Carrier E.field :=
    IsAbelianGalois.of_isCyclic _ _
  refine ⟨E, hab, he, hdegree, ?_⟩
  intro a ha
  apply mem_subgroup_of_index_dvd_ord F.canonicalTopologicalData H hU a
  rw [← hdegree]
  exact (unramifiedNormMembership p F (E.asPadicField (p := p))
    F.canonicalTopologicalData (E.asPadicField (p := p)).canonicalTopologicalData
    he a).mp ha

/-- The unramified containment assertion is satisfied without additional data. -/
theorem unramifiedNormSubgroupContainment (F : PadicField.{u} p)
    (H : Subgroup F.Carrierˣ) : UnramifiedNormSubgroupContainment F H := by
  intro hindex hU
  let : H.FiniteIndex := hindex
  exact exists_unramified_normSubgroup_le F H hU

end Langlands.ClassFieldTheory.Local
