import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentBaseChange

/-! # Isotropic vectors of the symmetric component from isotropic quaternionic vectors -/

noncomputable section

universe u v

open TensorProduct
open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (Q : QuatData F D)
  {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E

/-- Left multiplication by a quaternion, as an endomorphism over the ground field. -/
private def quaternionMul (a : D) : V →ₗ[F] V where
  toFun v := a • v
  map_add' v w := smul_add a v w
  map_smul' c v := by
    change a • (c • v) = c • (a • v)
    rw [← IsScalarTower.algebraMap_smul D c v, ← IsScalarTower.algebraMap_smul D c (a • v),
      smul_smul, smul_smul, Algebra.commutes (R := F) (A := D) c a]

private theorem quaternionMul_apply (a : D) (v : V) : quaternionMul (F := F) a v = a • v := rfl

variable (R : Type u) [Field R] [Algebra F R]

private theorem baseChange_quaternionMul_mul (a b : D) (t : R ⊗[F] V) :
    (quaternionMul (F := F) (V := V) (a * b)).baseChange R t =
      (quaternionMul (F := F) (V := V) a).baseChange R
        ((quaternionMul (F := F) (V := V) b).baseChange R t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
  | tmul r v =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      quaternionMul_apply, quaternionMul_apply, quaternionMul_apply, mul_smul]

private theorem baseChange_quaternionMul_algebraMap (f : F) (t : R ⊗[F] V) :
    (quaternionMul (F := F) (V := V) (algebraMap F D f)).baseChange R t =
      algebraMap F R f • t := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, ht, ht', smul_add]
  | tmul r v =>
    rw [LinearMap.baseChange_tmul, quaternionMul_apply, IsScalarTower.algebraMap_smul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      Algebra.smul_def, smul_eq_mul]

private theorem baseChange_quaternionMul_neg (a : D) (t : R ⊗[F] V) :
    (quaternionMul (F := F) (V := V) (-a)).baseChange R t =
      -((quaternionMul (F := F) (V := V) a).baseChange R t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', neg_add]
  | tmul r v =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, quaternionMul_apply,
      quaternionMul_apply, neg_smul, TensorProduct.tmul_neg]

private theorem baseChange_pair_quaternionMul_left (a : D) (x y : R ⊗[F] V) :
    (LinearMap.BilinMap.baseChange R B.toBilin)
        ((quaternionMul (F := F) (V := V) a).baseChange R x) y =
      ((1 : R) ⊗ₜ[F] a) * (LinearMap.BilinMap.baseChange R B.toBilin) x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
    | tmul s y =>
      rw [LinearMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul,
        LinearMap.BilinMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact congrArg ((r * s) ⊗ₜ[F] ·) (B.smul_left a x y)

private theorem baseChange_pair_quaternionMul_right (a : D) (x y : R ⊗[F] V) :
    (LinearMap.BilinMap.baseChange R B.toBilin) x
        ((quaternionMul (F := F) (V := V) a).baseChange R y) =
      (LinearMap.BilinMap.baseChange R B.toBilin) x y * ((1 : R) ⊗ₜ[F] τ a) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simp only [map_add, hy, hy', add_mul]
  | tmul s y =>
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', add_mul]
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul,
        LinearMap.BilinMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      exact congrArg ((r * s) ⊗ₜ[F] ·) (B.smul_right a x y)

variable [Algebra (field Q.c) R] [IsScalarTower F (field Q.c) R]

/-- The projection from the tensor over the ground field to the tensor over the embedded
quadratic field. -/
private def tensorToField :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    R ⊗[F] V →ₗ[R] R ⊗[E] V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : IsScalarTower F E V := ⟨fun a b x => by
    change (Q.ι (a • b)) • x = a • (Q.ι b • x)
    rw [map_smul, smul_assoc]⟩
  exact AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton R _ ((TensorProduct.mk E R V 1).restrictScalars F))

private theorem tensorToField_tmul :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ (r : R) (x : V), Q.tensorToField R (r ⊗ₜ[F] x) = r ⊗ₜ[E] x := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  intro r x
  change r • ((1 : R) ⊗ₜ[E] x) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A ground-field coordinate of the quaternion algebra, extended to the coefficients. -/
private def tensorCoefficient (f : D →ₗ[F] E) : R ⊗[F] D →ₗ[R] R :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton R _ ((Algebra.linearMap E R).restrictScalars F ∘ₗ f))

private theorem tensorCoefficient_tmul (f : D →ₗ[F] E) (r : R) (z : D) :
    tensorCoefficient Q R f (r ⊗ₜ[F] z) = r * algebraMap E R (f z) := rfl

private theorem symmetricComponent_tensorToField (x y : R ⊗[F] V) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    (LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar))
        (Q.tensorToField R x) (Q.tensorToField R y) =
      tensorCoefficient Q R ((κ).toLinearMap ∘ₗ Q.snd)
        ((LinearMap.BilinMap.baseChange R B.toBilin) x y) := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul s y =>
      simp only [Q.tensorToField_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinMap.baseChange_tmul, tensorCoefficient_tmul, symmetricComponent_apply,
        LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Algebra.smul_def]
      ring

/-- The operator `X + θ`, where `X` is left multiplication by the distinguished pure
quaternion and `θ` is the image of the root of the quadratic field. -/
private def plusRoot : R ⊗[F] V →ₗ[R] R ⊗[F] V :=
  (quaternionMul (F := F) (V := V) Q.x).baseChange R +
    algebraMap (field Q.c) R root • LinearMap.id

omit [IsScalarTower F (field Q.c) R] in
private theorem plusRoot_apply (t : R ⊗[F] V) :
    Q.plusRoot R t = (quaternionMul (F := F) (V := V) Q.x).baseChange R t +
      algebraMap (field Q.c) R root • t := rfl

private theorem algebraMap_root_mul_self :
    algebraMap (field Q.c) R root * algebraMap (field Q.c) R root = algebraMap F R Q.c := by
  rw [← map_mul, root_mul_self, ← IsScalarTower.algebraMap_apply]

private theorem tmul_smul_algebraMap (a : F) (r : R) (w : V) :
    r ⊗ₜ[F] (a • w) = algebraMap F R a • (r ⊗ₜ[F] w) := by
  rw [TensorProduct.tmul_smul, algebraMap_smul]

private theorem mul_tmul_eq_smul (A r : R) (w : V) :
    (A * r) ⊗ₜ[F] w = A • (r ⊗ₜ[F] w) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul]

omit [IsScalarTower F (field Q.c) R] in
private theorem plusRoot_tmul (r : R) (w : V) :
    Q.plusRoot R (r ⊗ₜ[F] w) =
      r ⊗ₜ[F] (Q.x • w) + algebraMap (field Q.c) R root • (r ⊗ₜ[F] w) := by
  rw [plusRoot_apply, LinearMap.baseChange_tmul, quaternionMul_apply]

/-- Left multiplication by the embedded field element `e` and multiplication by its image in
the coefficient field agree after applying `X + θ`. -/
private theorem plusRoot_tmul_ι_smul (e : field Q.c) (r : R) (v : V) :
    Q.plusRoot R (r ⊗ₜ[F] (Q.ι e • v)) =
      Q.plusRoot R ((algebraMap (field Q.c) R e * r) ⊗ₜ[F] v) := by
  obtain ⟨a₀, a₁, rfl⟩ := QuadField.exists_eq e
  have he : algebraMap (field Q.c) R (a₀ • (1 : field Q.c) + a₁ • root) =
      algebraMap F R a₀ + algebraMap F R a₁ * algebraMap (field Q.c) R root := by
    rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_one, mul_one,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hx2 : Q.x • Q.x • v = Q.c • v := by
    rw [smul_smul, Q.x_mul_x, IsScalarTower.algebraMap_smul]
  have hθ := Q.algebraMap_root_mul_self R
  rw [ι_linear, he, add_smul, smul_assoc, smul_assoc, one_smul, TensorProduct.tmul_add,
    tmul_smul_algebraMap, tmul_smul_algebraMap, mul_tmul_eq_smul, map_add, map_smul, map_smul,
    map_smul, plusRoot_tmul, plusRoot_tmul, hx2, tmul_smul_algebraMap, ← hθ]
  module

/-- The additive map whose composite with the projection `tensorToField` is `X + θ`. -/
private def fieldToTensor :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    R ⊗[E] V →+ R ⊗[F] V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  refine TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp
      ((TensorProduct.mk F R V).compr₂ ((Q.plusRoot R).restrictScalars F)).toAddMonoidHom) ?_
  intro e r v
  change Q.plusRoot R ((e • r) ⊗ₜ[F] v) = Q.plusRoot R (r ⊗ₜ[F] (Q.ι e • v))
  rw [Q.plusRoot_tmul_ι_smul, Algebra.smul_def]

private theorem fieldToTensor_tensorToField (t : R ⊗[F] V) :
    Q.fieldToTensor R (Q.tensorToField R t) = Q.plusRoot R t := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]
  | tmul r v =>
    rw [Q.tensorToField_tmul]
    rfl

include hbar in
/-- In characteristic different from two, let `B` be skew-hermitian for quaternion conjugation
in the coordinates `Q`. After extending scalars to a field containing the quadratic subfield,
a nonzero isotropic vector of `B` gives a nonzero isotropic vector of the extended symmetric
component. -/
theorem exists_isotropic_component_of_isotropic (h2 : (2 : F) ≠ 0) (t : R ⊗[F] V) (ht0 : t ≠ 0)
    (ht : LinearMap.BilinMap.baseChange R B.toBilin t t = 0) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∃ w : R ⊗[E] V, w ≠ 0 ∧
      LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar) w w = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  set B_R := LinearMap.BilinMap.baseChange R B.toBilin
  set X := (quaternionMul (F := F) (V := V) Q.x).baseChange R
  set J := (quaternionMul (F := F) (V := V) Q.j).baseChange R
  set θ := algebraMap (field Q.c) R root
  have hcomp (s : R ⊗[F] V) (hs : B_R s s = 0) :
      LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar)
        (Q.tensorToField R s) (Q.tensorToField R s) = 0 := by
    rw [Q.symmetricComponent_tensorToField B hbar R, hs, map_zero]
  have hJt : B_R (J t) (J t) = 0 := by
    rw [baseChange_pair_quaternionMul_left B R, baseChange_pair_quaternionMul_right B R, ht,
      zero_mul, mul_zero]
  by_cases hp : Q.tensorToField R t = 0
  · refine ⟨Q.tensorToField R (J t), ?_, hcomp _ hJt⟩
    intro hpJ
    have hplus : X t + θ • t = 0 := by
      have h := Q.fieldToTensor_tensorToField R t
      rw [hp, map_zero, plusRoot_apply] at h
      exact h.symm
    have hXJ : X (J t) = -(J (X t)) := by
      change (quaternionMul (F := F) (V := V) Q.x).baseChange R
          ((quaternionMul (F := F) (V := V) Q.j).baseChange R t) =
        -((quaternionMul (F := F) (V := V) Q.j).baseChange R
          ((quaternionMul (F := F) (V := V) Q.x).baseChange R t))
      rw [← baseChange_quaternionMul_mul, ← baseChange_quaternionMul_mul, Q.j_mul_x,
        baseChange_quaternionMul_neg, neg_neg]
    have hXt : X t = -(θ • t) := eq_neg_of_add_eq_zero_left hplus
    have hplusJ : Q.plusRoot R (J t) = (θ + θ) • J t := by
      rw [plusRoot_apply]
      change X (J t) + θ • J t = _
      rw [hXJ, hXt, map_neg, map_smul, neg_neg, add_smul]
    have hzero : (θ + θ) • J t = 0 := by
      rw [← hplusJ, ← Q.fieldToTensor_tensorToField R (J t), hpJ, map_zero]
    have hθ : θ ≠ 0 := by
      intro h
      have hroot : (root : field Q.c) = 0 :=
        (algebraMap (field Q.c) R).injective (h.trans (map_zero _).symm)
      have hx : Q.x = 0 := by rw [← Q.ι_root, hroot, map_zero]
      have hb := Q.basis.ne_zero 1
      rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at hb
      exact hb hx
    have h2R : (θ + θ) ≠ 0 := by
      rw [← two_mul]
      refine mul_ne_zero ?_ hθ
      have h := (algebraMap F R).injective.ne h2
      rwa [map_ofNat, map_zero] at h
    have hJ0 : J t = 0 := (smul_eq_zero.mp hzero).resolve_left h2R
    have hδ : algebraMap F R Q.δ ≠ 0 := by
      intro h
      have hδ0 : Q.δ = 0 := (algebraMap F R).injective (h.trans (map_zero _).symm)
      have hj := Q.j_mul_j
      rw [hδ0, map_zero] at hj
      have hb := Q.basis.ne_zero 2
      rw [show Q.basis 2 = Q.j from congrFun Q.basis_eq 2] at hb
      exact hb (mul_self_eq_zero.mp hj)
    have hJJ : J (J t) = algebraMap F R Q.δ • t := by
      change (quaternionMul (F := F) (V := V) Q.j).baseChange R
          ((quaternionMul (F := F) (V := V) Q.j).baseChange R t) = _
      rw [← baseChange_quaternionMul_mul, Q.j_mul_j, baseChange_quaternionMul_algebraMap]
    rw [hJ0, map_zero] at hJJ
    exact ht0 ((smul_eq_zero.mp hJJ.symm).resolve_left hδ)
  · exact ⟨Q.tensorToField R t, hp, hcomp t ht⟩

end Langlands.GroupScheme.KneserThree.QuatData
