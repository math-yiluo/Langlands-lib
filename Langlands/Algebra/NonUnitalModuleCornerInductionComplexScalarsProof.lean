import Langlands.Algebra.NonUnitalModuleCornerInductionComplexScalarsStatement

/-!
# Complex scalars on the actual corner-induction quotient

Proof of Renard I.3.2, the remark after (I.3.2.1), printed p.20 / PDF p.26.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerInduction

universe uA uZ

/-- The scalar actions induced from the complex algebra and the unital corner module
agree on the published balanced quotient. -/
theorem complexScalarsStatement : ComplexScalarsStatement.{uA, uZ} := by
  intro A _ _ _ _ e Z _ _
  have hmem (c : ℂ) : c • (e : A) ∈ e.corner := by
    apply (Idempotent.mem_corner_iff e _).mpr
    constructor
    · rw [mul_smul_comm, e.property.eq]
    · rw [smul_mul_assoc, e.property.eq]
  let k : ℂ →+* Idempotent.Corner e :=
    { toFun := fun c => ⟨c • (e : A), hmem c⟩
      map_zero' := Subtype.ext (zero_smul ℂ (e : A))
      map_one' := Subtype.ext (one_smul ℂ (e : A))
      map_add' := fun c d => Subtype.ext (add_smul c d (e : A))
      map_mul' := fun c d => Subtype.ext (by
        change (c * d) • (e : A) = (c • (e : A)) * (d • (e : A))
        rw [smul_mul_smul_comm, e.property.eq]) }
  constructor
  · refine ⟨Module.compHom Z k, fun c => ⟨k c, rfl, fun _ => rfl⟩⟩
  · let _ := tensorAddCommGroup e Z
    let _ := rightCornerModule e
    let _ := cornerModule e Z
    let b (c : ℂ) : A →+ Z →+ Tensor e Z :=
      { toFun := fun a =>
          { toFun := tmul e (c • a)
            map_zero' := NonUnitalModuleTensor.tmul_zero (Idempotent.Corner e) A Z _
            map_add' := NonUnitalModuleTensor.tmul_add (Idempotent.Corner e) A Z _ }
        map_zero' := AddMonoidHom.ext (fun z => by
          change tmul e (c • (0 : A)) z = 0
          rw [smul_zero]
          exact NonUnitalModuleTensor.zero_tmul (Idempotent.Corner e) A Z z)
        map_add' := fun a a' => AddMonoidHom.ext (fun z => by
          change tmul e (c • (a + a')) z =
            tmul e (c • a) z + tmul e (c • a') z
          rw [smul_add]
          exact NonUnitalModuleTensor.add_tmul (Idempotent.Corner e) A Z _ _ z) }
    have hb (c : ℂ) : NonUnitalModuleTensor.IsBalanced (Idempotent.Corner e) (b c) := by
      intro s a z
      change tmul e (c • (a * Idempotent.Corner.toAmbient e s)) z =
        tmul e (c • a) (s • z)
      rw [← smul_mul_assoc]
      exact tmul_balanced e s (c • a) z
    let f (c : ℂ) : AddMonoid.End (Tensor e Z) :=
      NonUnitalModuleTensor.lift (Idempotent.Corner e) (b c) (hb c)
    let r : ℂ →+* AddMonoid.End (Tensor e Z) :=
      { toFun := f
        map_zero' := by
          apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
          intro a z
          change tmul e ((0 : ℂ) • a) z = 0
          rw [zero_smul]
          exact NonUnitalModuleTensor.zero_tmul (Idempotent.Corner e) A Z z
        map_one' := by
          apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
          intro a z
          change tmul e ((1 : ℂ) • a) z = tmul e a z
          rw [one_smul]
        map_add' := fun c d => by
          apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
          intro a z
          change tmul e ((c + d) • a) z =
            tmul e (c • a) z + tmul e (d • a) z
          rw [add_smul]
          exact NonUnitalModuleTensor.add_tmul (Idempotent.Corner e) A Z _ _ z
        map_mul' := fun c d => by
          apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
          intro a z
          change tmul e ((c * d) • a) z = tmul e (c • (d • a)) z
          rw [mul_smul] }
    refine ⟨Module.compHom (Tensor e Z) r, ?_⟩
    intro c s hs a z
    constructor
    · rfl
    · change tmul e (c • a) z = tmul e a (s • z)
      calc
        tmul e (c • a) z = tmul e ((c • a) * (e : A)) z := by
          simpa only [Idempotent.Corner.toAmbient_one, one_smul] using
            (tmul_balanced e (1 : Idempotent.Corner e) (c • a) z).symm
        _ = tmul e (a * Idempotent.Corner.toAmbient e s) z := by
          rw [hs, smul_mul_assoc, mul_smul_comm]
        _ = tmul e a (s • z) := tmul_balanced e s a z

end Langlands.Algebra.NonUnitalModuleCornerInduction
