import Langlands.Representation.Parabolic.RefinedInductionTensorStatement

/-! Coordinate normalization for refined external tensor induction. -/

noncomputable section

open scoped BigOperators

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual refined Levi projection has the expected inner block coordinates. -/
theorem refinedLeviBlock_projection (q : refinedParabolic F.Carrier B S)
    (i : Fin B.length) :
    refinedLeviBlock B S i (refinedLeviProjection F.Carrier B S q) =
      (S i).leviProjection F.Carrier (refinedParabolicEval F.Carrier B S i q) := by
  change (refinedLeviEquiv F.Carrier B S).symm
      (refinedLeviEquiv F.Carrier B S
        (fun j => (S j).leviProjection F.Carrier
          (refinedParabolicEval F.Carrier B S j q))) i = _
  rw [MulEquiv.symm_apply_apply]

/-- The canonical positive half of the refined modulus is the product of the
canonical positive halves on the actual inner Levi coordinates. -/
theorem refinedLeviHalfModulus_eq_prod (m : refinedLevi F.Carrier B S) :
    T.refinedLeviHalfModulus B S m =
      ∏ i, T.leviHalfModulus (S i) (refinedLeviBlock B S i m) := by
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
      ((Units.map NNReal.sqrtHom.toMonoidHom) (T.refinedLeviModulus B S m)) = _
  rw [T.refinedLeviModulus_apply, map_prod, map_prod]
  rfl

/-- The refined parabolic normalizing character is the coordinatewise product. -/
theorem refinedParabolicHalfModulus_eq_prod (q : refinedParabolic F.Carrier B S) :
    T.refinedParabolicHalfModulus B S q =
      ∏ i, T.parabolicHalfModulus (S i) (refinedParabolicEval F.Carrier B S i q) := by
  rw [T.refinedParabolicHalfModulus_apply, T.refinedLeviHalfModulus_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [refinedLeviBlock_projection]
  rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.Parabolic.RefinedInductionTensor

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  (A : Factors.{uF, uV} F T B S)

/-- The individual normalized inducing actions, before smooth induction. -/
abbrev blockInducingRepresentation (i : Fin B.length) :=
  letI := T.topology
  twist (T.parabolicHalfModulus (S i))
    ((A i).representation.comp ((S i).leviProjection F.Carrier))

/-- The tensor of the normalized block inducing actions in actual subgroup coordinates. -/
def coordinateInducingRepresentation :=
  FiniteTensor.action (fun i =>
    (blockInducingRepresentation F T B S A i).comp
      (refinedParabolicEval F.Carrier B S i))

/-- The actual normalized refined inducing action from the published statement. -/
abbrev normalizedRefinedInducingRepresentation :=
  letI := T.topology
  twist (T.refinedParabolicHalfModulus B S)
    ((inducingRepresentation F T B S A).comp
      (refinedLeviProjection F.Carrier B S))

/-- Positive-half normalization commutes with this finite external tensor. -/
theorem coordinateInducingRepresentation_eq :
    coordinateInducingRepresentation F T B S A =
      normalizedRefinedInducingRepresentation F T B S A := by
  let := T.topology
  ext q v
  change FiniteTensor.action _ q (PiTensorProduct.tprod ℂ v) =
    (T.refinedParabolicHalfModulus B S q : ℂ) •
      inducingRepresentation F T B S A
        (refinedLeviProjection F.Carrier B S q) (PiTensorProduct.tprod ℂ v)
  rw [FiniteTensor.action_tprod]
  change PiTensorProduct.tprod ℂ (fun i =>
      (T.parabolicHalfModulus (S i) (refinedParabolicEval F.Carrier B S i q) : ℂ) •
        (A i).representation
          ((S i).leviProjection F.Carrier (refinedParabolicEval F.Carrier B S i q))
          (v i)) = _
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
  simp only [inducingRepresentation, MonoidHom.comp_apply, FiniteTensor.external_tprod]
  rw [T.refinedParabolicHalfModulus_eq_prod]
  simp only [Units.coe_prod, refinedLeviProjection, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply,
    MonoidHom.pi_apply]

end Langlands.Parabolic.RefinedInductionTensor
