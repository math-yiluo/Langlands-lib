import Langlands.Representation.IntegerLattice.NormalizedBlockNilpotenceStatement

/-! # Nilpotence and commutation of the actual normalized block differences -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- The normalized differences on the actual generalized-weight blocks commute
and vanish to the power given by the ambient dimension. -/
theorem commutingTupleNormalizedBlockNilpotence :
    CommutingTupleNormalizedBlockNilpotenceStatement.{u} := by
  intro d V _ _ _ A c
  constructor
  · intro i
    let G : Module.End ℂ (generalizedWeightBlock A c) :=
      generalizedWeightBlockGenerator A c i
    let f : Module.End ℂ V := A.1 i
    have hpow (n : ℕ) (w : generalizedWeightBlock A c) :
        (((G - (c i : ℂ) • 1) ^ n) w : V) =
          ((f - (c i : ℂ) • 1) ^ n) (w : V) := by
      induction n generalizing w with
      | zero => rfl
      | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
          Submodule.coe_smul]
        rw [show ∀ w : generalizedWeightBlock A c, (G w : V) = f (w : V) from
          fun w => generalizedWeightBlockGenerator_apply_coe A c i w, ih]
    have hzero : (G - (c i : ℂ) • 1) ^ Module.finrank ℂ V = 0 := by
      ext w
      rw [hpow]
      have hw := mem_generalizedWeightBlock.1 w.property i
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
        Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hw
      exact hw
    have hnormalize :
        normalizedGeneratorDifference A c i = (c i : ℂ)⁻¹ • (G - (c i : ℂ) • 1) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (c i).ne_zero, one_smul,
        normalizedGeneratorDifference, coe_normalizedBlockGenerator]
    rw [hnormalize, smul_pow, hzero, smul_zero]
  · intro i j
    have hG :
        Commute (generalizedWeightBlockGenerator A c i :
          Module.End ℂ (generalizedWeightBlock A c))
          (generalizedWeightBlockGenerator A c j :
            Module.End ℂ (generalizedWeightBlock A c)) := by
      rw [coe_generalizedWeightBlockGenerator, coe_generalizedWeightBlockGenerator]
      exact (Commute.all (generator d i) (generator d j)).map
        (generalizedWeightBlockRepresentation A c)
    unfold normalizedGeneratorDifference
    rw [coe_normalizedBlockGenerator, coe_normalizedBlockGenerator]
    exact ((hG.smul_left (c i : ℂ)⁻¹).smul_right (c j : ℂ)⁻¹).sub_left
      (Commute.one_left _)
      |>.sub_right (Commute.one_right _)

end Langlands
