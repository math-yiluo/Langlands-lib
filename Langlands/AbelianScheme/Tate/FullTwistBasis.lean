import Langlands.AbelianScheme.Tate.GeometricAdelicRankProof
import Langlands.AbelianScheme.Tate.TwistPrimeComparisonProof
import Langlands.AbelianScheme.Tate.TwistPrimeScalars
import Langlands.AbelianScheme.Tate.TwistRankProof
import Langlands.AbelianScheme.Tate.TwistRationalScalars

/-! # An integral basis of the full roots-of-unity Tate twist -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.TateTwist.Divisibility

open Global _root_.AlgebraicGeometry

universe u

local instance basisPrimeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local notation "ZR" => ProfiniteIntegerRing
local notation "Af" => FiniteAdeles ℚ
local notation "P" => (fun _ : ℕ => True)

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

private theorem nonempty_fullIntegralBasis : Nonempty (ZR ≃ₗ[ZR] Full K) := by
  obtain ⟨t, ht, _, _⟩ := fullPrimeProductComparison K
  let b (p : Nat.Primes) : (Fin 1 → PadicInt p) ≃ₗ[PadicInt p] TateTwist.Integral K p :=
    (LinearEquiv.funUnique (Fin 1) (PadicInt p) (PadicInt p)).trans
      (Classical.choice (integralRankOne K p inferInstance (Nat.cast_ne_zero.mpr p.property.ne_zero)))
  have he (x : Full K) : t x = toPrimeProduct K x := DFunLike.congr_fun ht x
  refine ⟨(LinearEquiv.funUnique (Fin 1) ZR ZR).symm.trans
    (TateAdelicRank.assemble 1 TateAdelicRank.fullScalarEquiv t ?_ b)⟩
  intro a x p
  rw [he, he]
  exact fullToPrime_smul K (p : ℕ) a x

/-- Over an algebraically closed field in characteristic zero the full
integral Tate twist admits a basis over the actual profinite integers. -/
def fullIntegralBasis : ZR ≃ₗ[ZR] Full K :=
  Classical.choice (nonempty_fullIntegralBasis K)

/-- The same basis written in the global sections of the geometric point. -/
def geometricFullIntegralBasis :
    ZR ≃ₗ[ZR] Full Γ(Spec (CommRingCat.of K), ⊤) :=
  (fullIntegralBasis K).trans
    (fullLinearEquiv P (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm)

variable {R : Type u} [CommRing R]

/-- Rationalizing a basis for the integral twist gives a basis over the
actual finite adeles, for the prescribed scalar comparison. -/
def finiteAdeleBasisOf (h : RationalProfiniteIntegerAdeleComparison)
    (b : ZR ≃ₗ[ZR] Full R) :
    letI := finiteAdeleModule R P h
    Af ≃ₗ[Af] RationalFull R := by
  letI := finiteAdeleModule R P h
  let f := LinearMap.toSpanSingleton Af (RationalFull R) (toRational R P (b 1))
  let e := (RationalProfiniteIntegerAdeleComparison.rationalEquiv h).toLinearEquiv.symm.trans
    ((b.toAddEquiv.toIntLinearEquiv).baseChange ℤ ℚ ZR (Full R))
  have he : ⇑f = ⇑e := by
    funext a
    obtain ⟨z, rfl⟩ := (RationalProfiniteIntegerAdeleComparison.rationalEquiv h).surjective a
    have hright : e (RationalProfiniteIntegerAdeleComparison.rationalEquiv h z) =
        ((b.toAddEquiv.toIntLinearEquiv).baseChange ℤ ℚ ZR (Full R)) z := by
      dsimp only [e, LinearEquiv.trans_apply]
      rw [show (RationalProfiniteIntegerAdeleComparison.rationalEquiv h).toLinearEquiv.symm
        (RationalProfiniteIntegerAdeleComparison.rationalEquiv h z) = z from
          (RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm_apply_apply z]
    rw [hright]
    clear hright
    change (f ∘ RationalProfiniteIntegerAdeleComparison.rationalEquiv h) z =
      ((b.toAddEquiv.toIntLinearEquiv).baseChange ℤ ℚ ZR (Full R)) z
    induction z using TensorProduct.inductionOn with
    | tmul q z =>
      change f (RationalProfiniteIntegerAdeleComparison.rationalEquiv h (q ⊗ₜ[ℤ] z)) =
        q ⊗ₜ[ℤ] b z
      rw [RationalProfiniteIntegerAdeleComparison.rationalEquiv_tmul,
        LinearMap.toSpanSingleton_apply, mul_smul]
      change finiteAdeleAction R P h (algebraMap ℚ Af q)
        (finiteAdeleAction R P h (RationalProfiniteIntegerAdeleComparison.integralEquiv h z)
          ((1 : ℚ) ⊗ₜ[ℤ] b 1)) = _
      rw [finiteAdeleAction_integral_tmul, finiteAdeleAction_diagonal, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one, ← b.map_smul, smul_eq_mul, mul_one]
    | add x y hx hy =>
      simpa only [Function.comp_apply, map_add] using congrArg₂ (· + ·) hx hy
  exact LinearEquiv.ofBijective f (he ▸ e.bijective)

/-- Under the integral scalar comparison, the adelic basis maps integral
scalars to the rationalizations of their values in the integral basis. -/
theorem finiteAdeleBasisOf_integral (h : RationalProfiniteIntegerAdeleComparison)
    (b : ZR ≃ₗ[ZR] Full R) (a : ZR) :
    letI := finiteAdeleModule R P h
    finiteAdeleBasisOf h b (RationalProfiniteIntegerAdeleComparison.integralEquiv h a) =
      toRational R P (b a) := by
  let := finiteAdeleModule R P h
  change finiteAdeleAction R P h (RationalProfiniteIntegerAdeleComparison.integralEquiv h a)
    ((1 : ℚ) ⊗ₜ[ℤ] b 1) = (1 : ℚ) ⊗ₜ[ℤ] b a
  rw [finiteAdeleAction_integral_tmul, ← b.map_smul, smul_eq_mul, mul_one]

end Langlands.TateTwist.Divisibility
