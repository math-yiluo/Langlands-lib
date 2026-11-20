import Langlands.ClassField.Global.TensorUnitNorm
import Langlands.Global.Arithmetic.NormModuloPowers
import Langlands.GroupScheme.Rational.KummerCocycleUnits

/-! # Norm-one torsion primitives after finite Galois refinement -/

noncomputable section

universe u

open groupCohomology
open scoped TensorProduct

namespace Langlands.ClassField.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Global Langlands.LocalClassField
open GroupScheme.KummerCocycle

set_option backward.isDefEq.respectTransparency false

variable {F B L : Type u} [Field F] [Field B] [Field L] [Algebra F B] [Algebra F L]
  [FiniteDimensional F B] [FiniteDimensional F L] [IsGalois F L]

omit [FiniteDimensional F L] [IsGalois F L] in
/-- If the differential has norm one, the norm of the primitive is a scalar crossed cocycle. -/
theorem tensorNorm_isMulCocycle (a : Gal(L/F) → (B ⊗[F] L)ˣ)
    (h : ∀ σ τ, tensorNormUnits F B L (tensorDifferential a σ τ) = 1) :
    IsMulCocycle₁ (fun σ => tensorNormUnits F B L (a σ)) := by
  intro σ τ
  have hh := h σ τ
  rw [tensorDifferential, map_mul, map_div, tensorNormUnits_action, div_mul_eq_mul_div] at hh
  exact (div_eq_one.mp hh).symm

/-- A torsion primitive of norm-one differential has a scalar Kummer radical for its norm. -/
theorem exists_tensorNorm_radical (n : ℕ) (a : Gal(L/F) → (B ⊗[F] L)ˣ)
    (ha : ∀ σ, a σ ^ n = 1)
    (h : ∀ σ τ, tensorNormUnits F B L (tensorDifferential a σ τ) = 1) :
    ∃ (s : Fˣ) (z : Lˣ), z ^ n = Units.map (algebraMap F L).toMonoidHom s ∧
      ∀ σ, value z σ = tensorNormUnits F B L (a σ) := by
  apply exists_radical n _ (tensorNorm_isMulCocycle a h)
  intro σ
  rw [← map_pow, ha, map_one]

/-- Existence of a norm-one torsion primitive on a finite Galois refinement. -/
def TensorNormOnePrimitiveAfterRefinement (n : ℕ)
    (c : Gal(L/F) × Gal(L/F) → (B ⊗[F] L)ˣ) : Prop :=
  ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M) (_ : IsGalois F M)
    (_ : Algebra L M) (_ : IsScalarTower F L M) (a : Gal(M/F) → (B ⊗[F] M)ˣ),
      (∀ σ, a σ ^ n = 1) ∧ (∀ σ, tensorNormUnits F B M (a σ) = 1) ∧
      ∀ σ τ, tensorDifferential a σ τ = extendTensorUnit M (c (σ.restrictNormal L, τ.restrictNormal L))

variable [Algebra B L] [IsScalarTower F B L] [Algebra.IsSeparable F B]

/-- If the norm of a torsion primitive is the Kummer cocycle of a norm modulo powers,
its differential has a norm-one torsion primitive on a finite Galois refinement. -/
theorem tensorNormOnePrimitiveAfterRefinement_of_normPower [CharZero F]
    (n : ℕ) (hn : n ≠ 0) (a : Gal(L/F) → (B ⊗[F] L)ˣ) (ha : ∀ σ, a σ ^ n = 1)
    {s : Fˣ} {z : Lˣ} (hz : z ^ n = Units.map (algebraMap F L).toMonoidHom s)
    (hnorm : ∀ σ, tensorNormUnits F B L (a σ) = value z σ)
    (hs : IsNormMulPower (E := B) n s) :
    TensorNormOnePrimitiveAfterRefinement n (fun p => tensorDifferential a p.1 p.2) := by
  obtain ⟨b, q, hb⟩ := hs
  obtain ⟨M, _, _, _, _, _, _, y, hy⟩ := exists_tensorUnit_root n hn (leftTensorUnit (F := F) (L := L) b)
  let : Algebra B M := Algebra.compHom M (algebraMap B L)
  let : IsScalarTower B L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F B M := IsScalarTower.of_algebraMap_eq fun t => by
    rw [IsScalarTower.algebraMap_apply F L M, IsScalarTower.algebraMap_apply B L M,
      ← IsScalarTower.algebraMap_apply F B L]
  let N := tensorNormUnits F B M
  let z' := Units.map (algebraMap L M).toMonoidHom z
  let q' := Units.map (algebraMap F M).toMonoidHom q
  have hq (σ : Gal(M/F)) : σ • q' = q' := Units.ext (σ.commutes (q : F))
  have hz' : z' ^ n = Units.map (algebraMap F M).toMonoidHom s := by
    dsimp only [z']
    rw [← map_pow, hz]
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F L M (s : F)).symm
  have hyN : N y ^ n = Units.map (algebraMap F M).toMonoidHom (normUnits F B b) := by
    rw [← map_pow, hy]
    change tensorNormUnits F B M (extendTensorUnit M (leftTensorUnit (F := F) (L := L) b)) = _
    rw [extendTensorUnit_leftTensorUnit, tensorNormUnits_left]
    rfl
  let r := z' / (N y * q')
  have hr : r ^ n = 1 := by
    dsimp only [r, q']
    rw [div_pow, mul_pow, hz', hyN, ← map_pow, ← map_mul, hb, div_self']
  obtain ⟨v, hv, hNv⟩ := exists_tensorNorm_torsion_lift (F := F) (B := B) n r hr
  let x := y * v
  have hx : x ^ n = (leftTensorUnit b : (B ⊗[F] M)ˣ) := by
    dsimp only [x]
    rw [mul_pow, hv, mul_one, hy, extendTensorUnit_leftTensorUnit]
  have hxN : N x = z' / q' := by
    change N (y * v) = _
    rw [map_mul, hNv]
    dsimp only [r]
    rw [← mul_div_assoc, mul_div_mul_left_eq_div]
  let ρ : Gal(M/F) →* Gal(L/F) := AlgEquiv.restrictNormalHom L
  let t (σ : Gal(M/F)) := extendTensorUnit M (a (ρ σ))
  let g := tensorCoboundary x
  have htN (σ : Gal(M/F)) : N (t σ) = σ • z' / z' := by
    change tensorNormUnits F B M (extendTensorUnit M (a (ρ σ))) = _
    rw [tensorNormUnits_extend, hnorm, value, map_div]
    have hmap : Units.map (algebraMap L M).toMonoidHom (ρ σ • z) = σ • z' :=
      Units.ext (σ.restrictNormal_commutes L (z : L))
    exact congrArg (fun w : Mˣ => w / z') hmap
  have hgN (σ : Gal(M/F)) : N (g σ) = σ • z' / z' := by
    change N (tensorAction F B M σ x / x) = _
    rw [map_div, show N (tensorAction F B M σ x) = _ from tensorNormUnits_action σ x,
      hxN, smul_div', hq, div_div_div_comm, div_self', div_one]
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fun σ => t σ / g σ, ?_, ?_, ?_⟩
  · intro σ
    change (extendTensorUnit M (a (ρ σ)) / (tensorAction F B M σ x / x)) ^ n = 1
    rw [div_pow, ← map_pow (extendTensorUnit M), ha, map_one, div_pow,
      ← map_pow (tensorAction F B M σ), hx, tensorAction_leftTensorUnit, div_self', div_self']
  · intro σ
    rw [map_div, htN σ, hgN σ, div_self']
  · intro σ τ
    change tensorAction F B M σ (t τ / g τ) / (t (σ * τ) / g (σ * τ)) * (t σ / g σ) =
      extendTensorUnit M (tensorDifferential a (ρ σ) (ρ τ))
    rw [map_div, div_div_div_comm, div_mul_div_comm,
      show tensorAction F B M σ (g τ) / g (σ * τ) * g σ = 1 from
        tensorDifferential_tensorCoboundary x σ τ, div_one]
    change tensorAction F B M σ (extendTensorUnit M (a (ρ τ))) /
      extendTensorUnit M (a (ρ (σ * τ))) * extendTensorUnit M (a (ρ σ)) = _
    rw [extendTensorUnit_action, map_mul ρ, ← map_div, ← map_mul]
    rfl

/-- For coprime degree and exponent the norm-correction condition is automatic. -/
theorem tensorNormOnePrimitiveAfterRefinement_of_coprime [CharZero F]
    (n : ℕ) (hn : n ≠ 0) (hB : (Module.finrank F B).Coprime n)
    (a : Gal(L/F) → (B ⊗[F] L)ˣ) (ha : ∀ σ, a σ ^ n = 1)
    (h : ∀ σ τ, tensorNormUnits F B L (tensorDifferential a σ τ) = 1) :
    TensorNormOnePrimitiveAfterRefinement n (fun p => tensorDifferential a p.1 p.2) := by
  obtain ⟨s, z, hz, hs⟩ := exists_tensorNorm_radical n a ha h
  exact tensorNormOnePrimitiveAfterRefinement_of_normPower n hn a ha hz (fun σ => (hs σ).symm)
    (isNormMulPower_of_coprime n hB s)

end Langlands.ClassField.Global.TensorUnitShapiro
