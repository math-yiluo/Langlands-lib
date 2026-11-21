import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentBaseChange

/-! # Isotropic planes in the symmetric component -/

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

private def mulLeftLinear (a : D) : V →ₗ[F] V where
  toFun v := a • v
  map_add' v w := smul_add a v w
  map_smul' c v := by
    change a • (c • v) = c • (a • v)
    rw [← IsScalarTower.algebraMap_smul D c v, ← IsScalarTower.algebraMap_smul D c (a • v),
      smul_smul, smul_smul, Algebra.commutes (R := F) (A := D) c a]

variable (R : Type u) [Field R] [Algebra F R]

private theorem baseChange_pair_mulLeft (a : D) (x y : R ⊗[F] V) :
    (LinearMap.BilinMap.baseChange R B.toBilin) ((mulLeftLinear (F := F) (V := V) a).baseChange R x) y =
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

private theorem baseChange_pair_mulRight (a : D) (x y : R ⊗[F] V) :
    (LinearMap.BilinMap.baseChange R B.toBilin) x ((mulLeftLinear (F := F) (V := V) a).baseChange R y) =
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

private def componentProjection :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    R ⊗[F] V →ₗ[R] R ⊗[E] V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : IsScalarTower F E V := ⟨fun a b x => by
    change (Q.ι (a • b)) • x = a • (Q.ι b • x)
    rw [map_smul, smul_assoc]⟩
  exact AlgebraTensorModule.lift (LinearMap.toSpanSingleton R _ ((TensorProduct.mk E R V 1).restrictScalars F))

private theorem componentProjection_tmul :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ (r : R) (x : V), Q.componentProjection R (r ⊗ₜ[F] x) = r ⊗ₜ[E] x := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  intro r x
  change r • ((1 : R) ⊗ₜ[E] x) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def coefficientOnTensor (f : D →ₗ[F] E) : R ⊗[F] D →ₗ[R] R :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton R _ ((Algebra.linearMap E R).restrictScalars F ∘ₗ f))

private theorem coefficientOnTensor_tmul (f : D →ₗ[F] E) (r : R) (z : D) :
    coefficientOnTensor Q R f (r ⊗ₜ[F] z) = r * algebraMap E R (f z) := rfl

private theorem symmetricComponent_projection (x y : R ⊗[F] V) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    (LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar)) (Q.componentProjection R x) (Q.componentProjection R y) =
      coefficientOnTensor Q R ((κ).toLinearMap ∘ₗ Q.snd) ((LinearMap.BilinMap.baseChange R B.toBilin) x y) := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul s y =>
      simp only [Q.componentProjection_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinMap.baseChange_tmul, coefficientOnTensor_tmul, symmetricComponent_apply,
        LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Algebra.smul_def]
      ring

private def firstComponent (y : V) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    V →ₗ[E] E := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  refine { toFun := fun x => Q.fst (B x y), map_add' := ?_, map_smul' := ?_ }
  · intro x x'
    rw [B.add_left, map_add]
  · intro a x
    change Q.fst (B (Q.ι a • x) y) = a * Q.fst (B x y)
    rw [B.smul_left, Q.fst_ι_mul]

private theorem firstComponent_zero_of_projection_zero (x y : R ⊗[F] V)
    (hx : Q.componentProjection R x = 0) :
    coefficientOnTensor Q R Q.fst ((LinearMap.BilinMap.baseChange R B.toBilin) x y) = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simp only [map_add, hy, hy', add_zero]
  | tmul r y =>
    let f : R ⊗[E] V →ₗ[R] R :=
      AlgebraTensorModule.lift (LinearMap.toSpanSingleton R _ ((Algebra.linearMap E R).comp (Q.firstComponent B y)))
    have hf : (coefficientOnTensor Q R Q.fst).comp ((LinearMap.BilinMap.baseChange R B.toBilin).flip (r ⊗ₜ[F] y)) =
        (r • f).comp (Q.componentProjection R) := by
      apply AlgebraTensorModule.ext
      intro s z
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.BilinMap.baseChange_tmul, coefficientOnTensor_tmul,
        Q.componentProjection_tmul, LinearMap.smul_apply]
      change (s * r) * algebraMap E R (Q.fst (B z y)) = r * (s * algebraMap E R (Q.fst (B z y)))
      ring
    have h := LinearMap.congr_fun hf x
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply, hx, map_zero] using h

/-- A nonsingular isotropic quaternion row produces two independent orthogonal
  isotropic vectors in the symmetric component after coefficient extension. -/
theorem exists_isotropic_pair_in_symmetricComponent (t s : R ⊗[F] V)
    (ht : (LinearMap.BilinMap.baseChange R B.toBilin) t t = 0)
    (hs : (LinearMap.BilinMap.baseChange R B.toBilin) t s = (1 : R) ⊗ₜ[F] (1 : D)) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    let H := (LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar))
    ∃ x y : R ⊗[E] V, LinearIndependent R ![x, y] ∧ H x x = 0 ∧ H x y = 0 ∧ H y y = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let p := Q.componentProjection (V := V) R
  let u := (mulLeftLinear (F := F) (V := V) Q.j).baseChange R t
  let T := (LinearMap.BilinMap.baseChange R B.toBilin)
  let H := (LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar))
  let f₁ := coefficientOnTensor Q R Q.fst
  let f₂ := coefficientOnTensor Q R ((κ).toLinearMap ∘ₗ Q.snd)
  have hcomp (x y : R ⊗[F] V) : H (p x) (p y) = f₂ (T x y) := Q.symmetricComponent_projection B hbar R x y
  have ht' : T t t = 0 := ht
  have htu : T t u = 0 := by
    change (LinearMap.BilinMap.baseChange R B.toBilin) t ((mulLeftLinear (F := F) (V := V) Q.j).baseChange R t) = 0
    rw [baseChange_pair_mulRight, ht, zero_mul]
  have huu : T u u = 0 := by
    change (LinearMap.BilinMap.baseChange R B.toBilin) ((mulLeftLinear (F := F) (V := V) Q.j).baseChange R t) u = 0
    rw [baseChange_pair_mulLeft, show (LinearMap.BilinMap.baseChange R B.toBilin) t u = 0 from htu, mul_zero]
  have hus : T u s = (1 : R) ⊗ₜ[F] Q.j := by
    change (LinearMap.BilinMap.baseChange R B.toBilin) ((mulLeftLinear (F := F) (V := V) Q.j).baseChange R t) s = _
    rw [baseChange_pair_mulLeft, hs, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hts : T t s = (1 : R) ⊗ₜ[F] (1 : D) := hs
  have hfst1 : Q.fst 1 = 1 := by simpa only [map_one] using Q.fst_ι 1
  have hsnd1 : Q.snd 1 = 0 := by simpa only [map_one] using Q.snd_ι 1
  have hfstj : Q.fst Q.j = 0 := by simpa only [map_one, mul_one] using Q.fst_j_mul 1
  have hsndj : Q.snd Q.j = 1 := by simpa only [map_one, mul_one] using Q.snd_j_mul 1
  refine ⟨p t, p u, ?_, ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro a b hab
    have hab' : p (a • t + b • u) = 0 := by simpa only [map_add, map_smul] using hab
    have ha := Q.firstComponent_zero_of_projection_zero B R (a • t + b • u) s hab'
    change f₁ (T (a • t + b • u) s) = 0 at ha
    have ha0 : a = 0 := by
      simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hts, hus, f₁, coefficientOnTensor_tmul,
        hfst1, hfstj, map_one, map_zero, mul_one, mul_zero, smul_zero, add_zero, smul_eq_mul] using ha
    refine ⟨ha0, ?_⟩
    have hb := congrArg (fun x => H x (p s)) hab
    have h₁ : H (p t) (p s) = 0 := by
      rw [hcomp, hts]
      simp [f₂, coefficientOnTensor_tmul, hsnd1]
    have h₂ : H (p u) (p s) = 1 := by
      rw [hcomp, hus]
      simp [f₂, coefficientOnTensor_tmul, hsndj]
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h₁, h₂, smul_eq_mul, mul_zero, mul_one,
      zero_add, map_zero, LinearMap.zero_apply] using hb
  · rw [hcomp, ht', map_zero]
  · rw [hcomp, htu, map_zero]
  · rw [hcomp, huu, map_zero]

/-- A quaternionic isotropic vector with a normalized partner gives a totally
  isotropic plane in the scalar extension of the symmetric component. -/
def SymmetricComponentIsotropicPairStatement : Prop :=
  ∀ (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
    (Q : QuatData F D) (τ : FirstKindInvolution F D) (V : Type v) [AddCommGroup V]
    [Module D V] [Module F V] [IsScalarTower F D V]
    (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)
    (R : Type u) [Field R] [Algebra F R] [Algebra (field Q.c) R] [IsScalarTower F (field Q.c) R]
    (t s : R ⊗[F] V), (LinearMap.BilinMap.baseChange R B.toBilin) t t = 0 →
    (LinearMap.BilinMap.baseChange R B.toBilin) t s = (1 : R) ⊗ₜ[F] (1 : D) →
    let K := field Q.c
    letI : Module K V := Module.compHom V Q.ι.toRingHom
    let H := LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar)
    ∃ x y : R ⊗[K] V, LinearIndependent R ![x, y] ∧ H x x = 0 ∧ H x y = 0 ∧ H y y = 0

theorem symmetricComponentIsotropicPair : SymmetricComponentIsotropicPairStatement.{u, v} := by
  intro F D _ _ _ Q τ V _ _ _ _ B hbar R _ _ _ _ t s ht hs
  exact Q.exists_isotropic_pair_in_symmetricComponent B hbar R t s ht hs

end Langlands.GroupScheme.KneserThree.QuatData
