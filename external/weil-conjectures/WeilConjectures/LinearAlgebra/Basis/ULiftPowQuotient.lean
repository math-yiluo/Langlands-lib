/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.LinearAlgebra.Basis.PowQuotientTower

/-!
# Truncations of `ULift R`

For an ideal `J` of a ring `R : Type`, the corresponding ideal `Ideal.uliftIdeal J` of
`ULift R` has `(ULift R ⧸ J'ⁿ⁺¹)^r ≅ ULift ((R ⧸ Jⁿ⁺¹)^r)` additively
(`Ideal.powQuotientULiftEquiv`), compatibly with the reduction maps
(`Ideal.powQuotientULiftEquiv_reduction`). This transports towers of `ULift 𝒪_E`-modules to the
discrete rings `(𝒪_E ⧸ ℓⁿ⁺¹)^r` of the continuous-map sheaves.
-/

@[expose] public section

universe v

namespace Ideal

variable {R : Type*} [CommRing R] (J : Ideal R) (r : ℕ)

/-- The ideal of `ULift R` corresponding to `J`. -/
abbrev uliftIdeal : Ideal (ULift.{v} R) := J.map (ULift.ringEquiv.symm : R ≃+* ULift.{v} R)

/-- The reduction `(R ⧸ Jⁿ⁺²)^r → (R ⧸ Jⁿ⁺¹)^r` as a ring homomorphism. -/
def powQuotientReductionRingHom (n : ℕ) : (Fin r → R ⧸ J ^ (n + 2)) →+* (Fin r → R ⧸ J ^ (n + 1)) :=
  RingHom.pi fun i ↦ (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).comp
    (Pi.evalRingHom _ i)

/-- The powers of `J` are the images of the powers of the corresponding ideal of `ULift R`. -/
lemma uliftIdeal_pow_map (n : ℕ) :
    J ^ n = ((uliftIdeal.{v} J) ^ n).map (ULift.ringEquiv : ULift.{v} R ≃+* R) := by
  rw [Ideal.map_pow]
  congr 1
  exact (Ideal.map_of_equiv (I := J) (ULift.ringEquiv.symm : R ≃+* ULift.{v} R)).symm

/-- `(ULift R ⧸ J'ⁿ⁺¹)^r ≅ ULift ((R ⧸ Jⁿ⁺¹)^r)` additively. -/
noncomputable def powQuotientULiftEquiv (n : ℕ) :
    (Fin r → ULift.{v} R ⧸ (uliftIdeal.{v} J) ^ (n + 1)) ≃+ ULift.{v} (Fin r → R ⧸ J ^ (n + 1)) :=
  (AddEquiv.piCongrRight fun _ ↦ (Ideal.quotientEquiv ((uliftIdeal.{v} J) ^ (n + 1)) (J ^ (n + 1))
    ULift.ringEquiv (uliftIdeal_pow_map J (n + 1))).toAddEquiv).trans AddEquiv.ulift.symm

/-- `powQuotientULiftEquiv` intertwines the reduction maps. -/
lemma powQuotientULiftEquiv_reduction [IsLocalRing (ULift.{v} R)] (n : ℕ)
    (x : Fin r → ULift.{v} R ⧸ (uliftIdeal.{v} J) ^ (n + 2)) :
    powQuotientULiftEquiv J r n ((uliftIdeal.{v} J).powQuotientReduction r n x) =
      ULift.up (J.powQuotientReductionRingHom r n (powQuotientULiftEquiv J r (n + 1) x).down) := by
  refine congrArg ULift.up (funext fun i ↦ ?_)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x i)
  change Ideal.quotientEquiv ((uliftIdeal.{v} J) ^ (n + 1)) (J ^ (n + 1)) ULift.ringEquiv
      (uliftIdeal_pow_map J (n + 1)) (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (x i)) =
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (Ideal.quotientEquiv ((uliftIdeal.{v} J) ^ (n + 2)) (J ^ (n + 2)) ULift.ringEquiv
        (uliftIdeal_pow_map J (n + 2)) (x i))
  rw [← ha, Ideal.Quotient.factor_mk, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk,
    Ideal.Quotient.factor_mk]

end Ideal
