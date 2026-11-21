import Langlands.GroupScheme.Quaternionic.SkewHermitianQuadraticComponent

/-! # The pure-line coefficient of a scalar-extended quaternionic self-value -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree

namespace Presentation

variable {A B : Type*} [CommRing A] [Ring B] (P : Presentation A B)

/-- The first coefficient of a conjugated pure element is the pure scalar
  times the sum of the two coefficient norms weighted by `1` and `j²`. -/
theorem fst_mul_pure_mul_bar (z : B) (s : A) (hs : P.c.bar s = -s) :
    P.fst (z * P.ι s * P.bar z) =
      s * (P.fst z * P.c.bar (P.fst z) + P.δ * (P.snd z * P.c.bar (P.snd z))) := by
  simp only [fst_mul, snd_mul, fst_bar, snd_bar, fst_ι, snd_ι, mul_zero, add_zero, zero_add,
    map_mul, hs]
  ring

end Presentation

namespace QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  (R : Type u) [CommRing R] [Algebra F R]

local notation "E" => field Q.c
local notation "r" => (root : field Q.c)
local notation "P" => Q.presentation R

/-- The two coordinates `1` and `root` still span after extending scalars. -/
theorem exists_quadraticTensorCoordinates (z : E ⊗[F] R) :
    ∃ a b : R, z = (1 : E) ⊗ₜ[F] a + r ⊗ₜ[F] b := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨a, b, hx⟩ := QuadField.exists_eq x
    refine ⟨a • y, b • y, ?_⟩
    rw [hx, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  | add z w hz hw =>
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨a', b', rfl⟩ := hw
    refine ⟨a + a', b + b', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add, add_add_add_comm]

/-- The norm in the scalar-extended quadratic subalgebra has its explicit
  two-coordinate expression over the new coefficient ring. -/
theorem quadraticTensor_mul_conjugate (a b : R) :
    let z := (1 : E) ⊗ₜ[F] a + r ⊗ₜ[F] b
    z * (Q.tensorInvolution R).bar z = (1 : E) ⊗ₜ[F] (a ^ 2 - algebraMap F R Q.c * b ^ 2) := by
  dsimp only
  have h₁ : ((1 : E) ⊗ₜ[F] a) ^ 2 = (1 : E) ⊗ₜ[F] (a ^ 2) := by
    rw [sq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, sq]
  have h₂ : (r ⊗ₜ[F] b) ^ 2 = (1 : E) ⊗ₜ[F] (algebraMap F R Q.c * b ^ 2) := by
    have hc : algebraMap F E Q.c = Q.c • (1 : E) := by rw [Algebra.smul_def, mul_one]
    rw [sq, Algebra.TensorProduct.tmul_mul_tmul, QuadField.root_mul_self, hc,
      TensorProduct.smul_tmul, Algebra.smul_def, sq]
  rw [map_add, Q.tensorInvolution_tmul, Q.tensorInvolution_tmul, map_one, QuadField.conjugation_root,
    TensorProduct.neg_tmul, ← sub_eq_add_neg, show ∀ x y : E ⊗[F] R,
      (x + y) * (x - y) = x ^ 2 - y ^ 2 by intro x y; ring, h₁, h₂, TensorProduct.tmul_sub]

/-- The abstract first-coefficient identity applies to the actual scalar extension
  of the quaternionic involution and the embedded pure root line. -/
theorem fstR_mul_pure_mul_baseChange (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z)
    (z : R ⊗[F] D) (a : R) :
    Q.fstR R (z * (a ⊗ₜ[F] Q.x) * τ.baseChange R z) =
      (r ⊗ₜ[F] a) * ((P).fst z * (P).c.bar ((P).fst z) +
        (P).δ * ((P).snd z * (P).c.bar ((P).snd z))) := by
  have hbase (z : R ⊗[F] D) : (P).bar z = τ.baseChange R z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x => rw [Q.presentation_bar_tmul, FirstKindInvolution.baseChange_tmul, hbar]
    | add z w hz hw => rw [(P).bar_add, FirstKindInvolution.map_add, hz, hw]
  have hi : (P).ι (r ⊗ₜ[F] a) = a ⊗ₜ[F] Q.x := by
    change Q.ιR R (r ⊗ₜ[F] a) = _
    rw [Q.ιR_tmul, Q.ι_root]
  have hs : (P).c.bar (r ⊗ₜ[F] a) = -(r ⊗ₜ[F] a) := by
    change (Q.tensorInvolution R).bar _ = _
    rw [Q.tensorInvolution_tmul, QuadField.conjugation_root, TensorProduct.neg_tmul]
  rw [← hbase, ← hi]
  exact (P).fst_mul_pure_mul_bar z (r ⊗ₜ[F] a) hs

/-- The coefficient identity over a scalar extension of the quaternion algebra. -/
def PureTensorCoefficientStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [DivisionRing D] [Algebra F D] [CommRing R] [Algebra F R]
    (Q : QuatData F D) (τ : FirstKindInvolution F D), (∀ z, τ z = Q.bar z) →
    ∀ (z : R ⊗[F] D) (a : R),
    let p := Q.presentation R
    Q.fstR R (z * (a ⊗ₜ[F] Q.x) * τ.baseChange R z) =
      ((root : field Q.c) ⊗ₜ[F] a) * (p.fst z * p.c.bar (p.fst z) +
        p.δ * (p.snd z * p.c.bar (p.snd z)))

theorem pureTensorCoefficient : PureTensorCoefficientStatement.{u} := by
  intro F D R _ _ _ _ _ Q τ hbar z a
  exact Q.fstR_mul_pure_mul_baseChange R τ hbar z a

end QuatData

end Langlands.GroupScheme.KneserThree
