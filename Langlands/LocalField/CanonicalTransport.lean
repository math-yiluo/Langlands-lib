import Langlands.Weil.Local.ExtensionResidue
import Langlands.LocalField.Normalization.Proof

/-! # Arithmetic transport under a p-adic algebra equivalence -/

noncomputable section

namespace Langlands.PadicField.CanonicalTransport

open Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- The existing residue maps in the two directions form a residue-field equivalence. -/
def residueEquiv : F.canonicalTopologicalData.ResidueField ≃+*
    E.canonicalTopologicalData.ResidueField :=
  { extensionResidueMap F E e.toAlgHom with
    invFun := extensionResidueMap E F e.symm.toAlgHom
    left_inv := by
      intro x
      change ((extensionResidueMap E F e.symm.toAlgHom).comp
        (extensionResidueMap F E e.toAlgHom)) x = x
      rw [← extensionResidueMap_comp]
      have h : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id (Padic p) F.Carrier := by
        ext x
        exact e.symm_apply_apply x
      rw [h, extensionResidueMap_id]
      rfl
    right_inv := by
      intro x
      change ((extensionResidueMap F E e.toAlgHom).comp
        (extensionResidueMap E F e.symm.toAlgHom)) x = x
      rw [← extensionResidueMap_comp]
      have h : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id (Padic p) E.Carrier := by
        ext x
        exact e.apply_symm_apply x
      rw [h, extensionResidueMap_id]
      rfl }

@[simp] theorem residueEquiv_residue (x : F.canonicalTopologicalData.Integers) :
    residueEquiv F E e (F.canonicalTopologicalData.residue x) =
      E.canonicalTopologicalData.residue (extensionIntegerMap F E e.toAlgHom x) := rfl

include e in
/-- The canonical residue cardinalities agree under an actual algebra equivalence. -/
theorem residueCardinality_eq :
    E.canonicalTopologicalData.residueCardinality = F.canonicalTopologicalData.residueCardinality :=
  (Nat.card_congr (residueEquiv F E e).toEquiv).symm

/-- The residue-cardinality normalized absolute value is preserved. -/
theorem normalizedAbs_map (x : F.Carrier) :
    E.canonicalTopologicalData.normalizedAbs (e x) =
      F.canonicalTopologicalData.normalizedAbs x := by
  rw [TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree,
    TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree,
    show E.canonicalNorm (e x) = F.canonicalNorm x from canonicalNorm_map F E e.toAlgHom x,
    e.toLinearEquiv.finrank_eq]

/-- The integer order is preserved, including its specified convention at zero. -/
theorem ord_map (x : F.Carrier) :
    E.canonicalTopologicalData.ord (e x) = F.canonicalTopologicalData.ord x := by
  by_cases hx : x = 0
  · simp [hx, TopologicalData.ord_zero]
  have he : e x ≠ 0 := by simpa only [map_zero] using e.injective.ne hx
  have h := normalizedAbs_map F E e x
  rw [E.canonicalTopologicalData.normalizedAbs_of_ne_zero he,
    F.canonicalTopologicalData.normalizedAbs_of_ne_zero hx, residueCardinality_eq F E e] at h
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq) h)

/-- The actual normalized discrete valuations are preserved, including zero. -/
theorem discreteValuation_map (x : F.Carrier) :
    E.canonicalTopologicalData.discreteValuation (e x) =
      F.canonicalTopologicalData.discreteValuation x := by
  by_cases hx : x = 0
  · simp [hx]
  have he : e x ≠ 0 := by simpa only [map_zero] using e.injective.ne hx
  have h := congrArg Neg.neg (ord_map F E e x)
  simp only [TopologicalData.ord, neg_neg] at h
  have he0 := (E.canonicalTopologicalData.discreteValuation.ne_zero_iff).mpr he
  have hx0 := (F.canonicalTopologicalData.discreteValuation.ne_zero_iff).mpr hx
  simpa only [WithZero.exp_log he0, WithZero.exp_log hx0] using congrArg WithZero.exp h

end Langlands.PadicField.CanonicalTransport
