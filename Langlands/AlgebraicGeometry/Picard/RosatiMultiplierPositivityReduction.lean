import Langlands.AlgebraicGeometry.Picard.RosatiMultiplierPositivityStatement
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityReduction
import Langlands.AlgebraicGeometry.Picard.RosatiRationalInverseProof

/-! # From actual Rosati positivity to positive self-isogeny multipliers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

/-- The full existing Rosati positivity statement implies the full existing
multiplier positivity statement, at the same arbitrary universe. -/
def MultiplierPositivityReductionStatement : Prop :=
  PositivityStatement.{u} → MultiplierPositivityStatement.{u}

variable {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (P : Prerequisites.{u}) (W : DualData A) (hadd : W.Additivity P)
  (lam : A ⟶ W.dual P) [HasRationalInverse P W lam]

private theorem involution_identity :
    involution P W hadd lam (id0 A) = id0 A := by
  have hid : W.dual0 P hadd (id0 A) = id0 (W.dual P) :=
    dualHom0_id P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability W.hasDual W.inversePoincare W.evaluation
      W.geometry hadd
  rw [involution_apply, hid, comp0_id0, polarization_comp_inverse]

/-- Composing the existing actual dual-pullback equation with the inverse
polarization gives the Rosati norm equation on the same rational morphism. -/
theorem involution_mul_self_of_pullback (f : End0 A) (q : ℚ)
    (hf : IsRationalDualPullbackMultiple P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability
      W.hasDual W.hasDual W.geometry W.geometry
      W.inversePoincare W.evaluation W.inversePoincare W.evaluation
      hadd q f (homToHom0 lam) (homToHom0 lam)) :
    involution P W hadd lam f * f = q • id0 A := by
  change comp0 A (W.dual P) (W.dual P)
      (comp0 A A (W.dual P) f (homToHom0 lam)) (W.dual0 P hadd f) =
    q • homToHom0 lam at hf
  have h := congrArg
    (fun t => comp0 A (W.dual P) A t (polarizationInverse P W lam)) hf
  simpa only [end0_mul, involution_apply, comp0_assoc, map_smul,
    LinearMap.smul_apply, polarization_comp_inverse] using h

/-- The unchanged positivity target implies the unchanged multiplier target.
Rational invertibility is supplied by the published geometric theorem. -/
theorem multiplierPositivity_of_positivity
    (hpositive : PositivityStatement.{u}) : MultiplierPositivityStatement.{u} := by
  intro P k _ _ _ A W hadd lam hlam hA e q hq
  let : HasRationalInverse P W lam := rationalInverse P k A W lam hlam
  have hf : e.hom ≠ (0 : End0 A) := by
    intro hz
    have h := e.hom_inv_id
    change comp0 A A A e.hom e.inv = id0 A at h
    simp only [hz, map_zero] at h
    exact hA h.symm
  have hnorm := involution_mul_self_of_pullback P W hadd lam e.hom (q : ℚ) hq
  have hstrict := (hpositive P k A W hadd lam hlam).2.2
  have htrace : 0 < geometricEndomorphismTrace A (id0 A) := by
    have h := hstrict (id0 A) hA
    rw [involution_identity] at h
    simpa only [end0_mul, id0_comp0] using h
  have hprod : 0 < (q : ℚ) * geometricEndomorphismTrace A (id0 A) := by
    have h := hstrict e.hom hf
    rw [geometricEndomorphismTrace_mul_comm A e.hom (involution P W hadd lam e.hom),
      hnorm, map_smul, smul_eq_mul] at h
    exact h
  exact (mul_pos_iff_of_pos_right htrace).mp hprod

end Langlands.AbelianScheme.Rosati
