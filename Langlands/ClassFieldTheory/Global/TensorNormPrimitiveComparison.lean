import Langlands.ClassFieldTheory.Global.TensorNormOnePrimitive
import Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof
import Langlands.ClassFieldTheory.Local.UnitInvariants

/-! # Recovering a base norm class from a norm-one torsion primitive -/

noncomputable section

universe u

open groupCohomology
open scoped TensorProduct

namespace Langlands.ClassFieldTheory.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Global Langlands.LocalClassField
open ClassFieldTheory.Local GroupScheme.KummerCocycle

set_option backward.isDefEq.respectTransparency false

variable {F B L : Type u} [Field F] [Field B] [Field L] [Algebra F B] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

/-- A fixed tensor unit in characteristic zero comes from the actual left factor. -/
theorem exists_leftTensorUnit_of_fixed [CharZero F] (x : (B ⊗[F] L)ˣ)
    (h : ∀ σ : Gal(L/F), tensorAction F B L σ x = x) :
    ∃ b : Bˣ, leftTensorUnit b = x := by
  obtain ⟨b, hb⟩ := IdeleGaloisDescentProof.exists_tmul_one_of_lTensor_aut_eq (x : B ⊗[F] L)
    (fun σ => congrArg Units.val (h σ))
  have hb₀ : b ≠ 0 := by
    intro he
    apply x.ne_zero
    rw [← hb, he, TensorProduct.zero_tmul]
  exact ⟨Units.mk0 b hb₀, Units.ext hb⟩

private theorem exists_scalarUnit_of_fixed (x : Lˣ) (h : ∀ σ : Gal(L/F), σ • x = x) :
    ∃ a : Fˣ, Units.map (algebraMap F L).toMonoidHom a = x := by
  let t : (unitsRepresentation F L).ρ.invariants := ⟨Additive.ofMul x, fun σ => h σ⟩
  obtain ⟨a, ha⟩ := baseUnitsToInvariants_surjective F L t
  exact ⟨a.toMul, congrArg (fun z : (unitsRepresentation F L).ρ.invariants =>
    Additive.toMul (z.val : Additive Lˣ)) ha⟩

variable [Algebra B L] [IsScalarTower F B L] [FiniteDimensional F B] [Algebra.IsSeparable F B]

/-- If a torsion cochain with scalar norm radical has the same differential as a norm-one
  torsion cochain, its scalar radicand is a norm modulo powers. -/
def TensorNormPrimitiveComparisonStatement : Prop :=
  ∀ (n : ℕ) (a b : Gal(L/F) → (B ⊗[F] L)ˣ),
    (∀ σ, a σ ^ n = 1) → (∀ σ, b σ ^ n = 1) →
    (∀ σ, tensorNormUnits F B L (b σ) = 1) →
    (∀ σ τ, tensorDifferential a σ τ = tensorDifferential b σ τ) →
    ∀ (s : Fˣ) (z : Lˣ), z ^ n = Units.map (algebraMap F L).toMonoidHom s →
      (∀ σ, tensorNormUnits F B L (a σ) = value z σ) → IsNormMulPower (E := B) n s

/-- Tensor-unit Hilbert 90 and fixed-point descent extract the actual norm factorization. -/
theorem tensorNormPrimitiveComparison [CharZero F] :
    TensorNormPrimitiveComparisonStatement (F := F) (B := B) (L := L) := by
  intro n a b ha hb hn hdiff s z hz hnorm
  let c (σ : Gal(L/F)) := a σ / b σ
  have hc (σ τ : Gal(L/F)) : c (σ * τ) = tensorAction F B L σ (c τ) * c σ := by
    have h : tensorDifferential c σ τ = 1 := by
      change tensorAction F B L σ (a τ / b τ) / (a (σ * τ) / b (σ * τ)) * (a σ / b σ) = 1
      rw [map_div, div_div_div_comm, div_mul_div_comm,
        show tensorAction F B L σ (a τ) / a (σ * τ) * a σ =
          tensorAction F B L σ (b τ) / b (σ * τ) * b σ from hdiff σ τ, div_self']
    change tensorAction F B L σ (c τ) / c (σ * τ) * c σ = 1 at h
    rw [div_mul_eq_mul_div] at h
    exact (div_eq_one.mp h).symm
  obtain ⟨x, hx⟩ := exists_tensorCoboundary c hc
  have hfix (σ : Gal(L/F)) : tensorAction F B L σ (x ^ n) = x ^ n := by
    apply div_eq_one.mp
    rw [map_pow, ← div_pow, show tensorAction F B L σ x / x = a σ / b σ from hx σ,
      div_pow, ha, hb, div_self']
  obtain ⟨y, hy⟩ := exists_leftTensorUnit_of_fixed (x ^ n) hfix
  let N := tensorNormUnits F B L
  have hNx (σ : Gal(L/F)) : σ • N x / N x = value z σ := by
    have h := congrArg N (hx σ)
    change N (tensorAction F B L σ x / x) = N (a σ / b σ) at h
    rw [map_div, map_div, show N (tensorAction F B L σ x) = _ from tensorNormUnits_action σ x,
      show N (a σ) = _ from hnorm σ, show N (b σ) = 1 from hn σ, div_one] at h
    exact h
  have hqfix (σ : Gal(L/F)) : σ • (z / N x) = z / N x := by
    apply div_eq_one.mp
    rw [smul_div', div_div_div_comm, ← value, ← hNx, div_self']
  obtain ⟨q, hq⟩ := exists_scalarUnit_of_fixed (z / N x) hqfix
  let j := Units.map (algebraMap F L).toMonoidHom
  have hrad : N x * j q = z := by
    rw [show j q = z / N x from hq, mul_comm, div_mul_cancel]
  refine ⟨y, q, ?_⟩
  have hinj : Function.Injective j := fun u v h =>
    Units.ext ((algebraMap F L).injective (congrArg Units.val h))
  apply hinj
  have hyN : N (leftTensorUnit y) = j (normUnits F B y) := tensorNormUnits_left y
  rw [map_mul, map_pow, ← hyN, hy, map_pow, ← mul_pow, hrad]
  exact hz

end Langlands.ClassFieldTheory.Global.TensorUnitShapiro
