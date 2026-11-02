import Langlands.AlgebraicGeometry.GroupoidCoactionExact
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Module.TransferInstance

/-! # Tensor reassociation for the two actions of an affine relation -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable (t : B →+* C)

namespace GroupoidCoaction

/-- A separate copy of the relation ring carrying its target algebra structure. -/
structure TargetRing (_t : B →+* C) where
  val : C

def targetRingEquiv : TargetRing t ≃ C where
  toFun := TargetRing.val
  invFun := TargetRing.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommRing (TargetRing t) := (targetRingEquiv t).commRing

def targetRingIso : TargetRing t ≃+* C := (targetRingEquiv t).ringEquiv

instance : Algebra B (TargetRing t) := ((targetRingIso t).symm.toRingHom.comp t).toAlgebra

omit [Algebra B C] in
@[simp] lemma targetRing_mk_zero : (TargetRing.mk 0 : TargetRing t) = 0 := rfl
omit [Algebra B C] in
@[simp] lemma targetRing_mk_add (x y : C) :
    (TargetRing.mk (x + y) : TargetRing t) = TargetRing.mk x + TargetRing.mk y := rfl
omit [Algebra B C] in
@[simp] lemma targetRing_mk_mul (x y : C) :
    (TargetRing.mk (x * y) : TargetRing t) = TargetRing.mk x * TargetRing.mk y := rfl

/-- The usual tensor module, with scalars on the coefficients restricted along `t`. -/
structure TargetModule (_t : B →+* C) (M : Type v) [AddCommGroup M] [Module B M] where
  val : C ⊗[B] M

def targetModuleEquiv (M : Type v) [AddCommGroup M] [Module B M] :
    TargetModule t M ≃ C ⊗[B] M where
  toFun := TargetModule.val
  invFun := TargetModule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (M : Type v) [AddCommGroup M] [Module B M] :
    AddCommGroup (TargetModule t M) := (targetModuleEquiv t M).addCommGroup

def targetModuleAddEquiv (M : Type v) [AddCommGroup M] [Module B M] :
    TargetModule t M ≃+ C ⊗[B] M where
  __ := targetModuleEquiv t M
  map_add' _ _ := rfl

instance (M : Type v) [AddCommGroup M] [Module B M] :
    Module C (TargetModule t M) := (targetModuleAddEquiv t M).module C

instance (M : Type v) [AddCommGroup M] [Module B M] :
    Module B (TargetModule t M) := Module.compHom (TargetModule t M) t

/-- The ring of composable pairs, with its final source algebra structure. -/
structure PairRing (t : B →+* C) where
  val : C ⊗[B] TargetRing t

def pairRingEquiv : PairRing t ≃ C ⊗[B] TargetRing t where
  toFun := PairRing.val
  invFun := PairRing.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommRing (PairRing t) := (pairRingEquiv t).commRing

def pairRingIso : PairRing t ≃+* C ⊗[B] TargetRing t := (pairRingEquiv t).ringEquiv

@[simp] lemma pairRing_mk_zero : (PairRing.mk 0 : PairRing t) = 0 := rfl
@[simp] lemma pairRing_mk_add (x y : C ⊗[B] TargetRing t) :
    (PairRing.mk (x + y) : PairRing t) = PairRing.mk x + PairRing.mk y := rfl

def pairFirst : C →+* PairRing t :=
  (pairRingIso t).symm.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom

def pairSecondHom : C →+* PairRing t :=
  (pairRingIso t).symm.toRingHom.comp
    (Algebra.TensorProduct.includeRight.toRingHom.comp (targetRingIso t).symm.toRingHom)

instance : Algebra B (PairRing t) :=
  ((pairSecondHom t).comp (algebraMap B C)).toAlgebra

def pairSecond : C →ₐ[B] PairRing t where
  toRingHom := pairSecondHom t
  commutes' _ := rfl

lemma pairRing_smul_val (b : B) (x : PairRing t) :
    (b • x).val = ((1 : C) ⊗ₜ[B] TargetRing.mk (algebraMap B C b)) * x.val := by
  rw [Algebra.smul_def]
  rfl

lemma pair_compat :
    (pairFirst t).comp (algebraMap B C) =
      (pairSecond t : C →+* PairRing t).comp t := by
  ext b
  apply (pairRingEquiv t).injective
  change (algebraMap B C b) ⊗ₜ[B] (1 : TargetRing t) =
    (1 : C) ⊗ₜ[B] algebraMap B (TargetRing t) b
  simpa only [Algebra.smul_def, mul_one] using
    (TensorProduct.smul_tmul (R := B) b (1 : C) (1 : TargetRing t))

variable {t}
variable {M : Type v} [AddCommGroup M] [Module B M]

@[simp] lemma targetModule_mk_zero : (TargetModule.mk 0 : TargetModule t M) = 0 := rfl
@[simp] lemma targetModule_mk_add (x y : C ⊗[B] M) :
    (TargetModule.mk (x + y) : TargetModule t M) = TargetModule.mk x + TargetModule.mk y := rfl

/-- The coaction as an ordinary linear map after restriction along the target. -/
def targetLinearMap (θ : GroupoidCoaction t M) : M →ₗ[B] TargetModule t M where
  toFun m := ⟨θ.coaction m⟩
  map_add' m n := by apply (targetModuleEquiv t M).injective; exact θ.coaction.map_add m n
  map_smul' b m := by apply (targetModuleEquiv t M).injective; exact θ.map_smul b m

variable (t M)

/-- Reassociate a tensor over the two different object-ring actions. -/
def pairTensorMap : C ⊗[B] TargetModule t M →+ PairRing t ⊗[B] M :=
  liftAddHom
    { toFun := fun c =>
        (liftAddHom
          { toFun := fun c' : C =>
              { toFun := fun m => (PairRing.mk (c ⊗ₜ[B] TargetRing.mk c')) ⊗ₜ[B] m
                map_zero' := by simp
                map_add' := fun m n => TensorProduct.tmul_add _ m n }
            map_zero' := by ext m; simp
            map_add' := by
              intro x y
              ext m
              simp [TensorProduct.tmul_add, TensorProduct.add_tmul] }
          (fun b c' m => by
            change (PairRing.mk (c ⊗ₜ[B] TargetRing.mk (b • c'))) ⊗ₜ[B] m =
              (PairRing.mk (c ⊗ₜ[B] TargetRing.mk c')) ⊗ₜ[B] (b • m)
            rw [← TensorProduct.smul_tmul]
            congr 1
            apply (pairRingEquiv t).injective
            change c ⊗ₜ[B] TargetRing.mk (b • c') = (b • _ : PairRing t).val
            rw [pairRing_smul_val]
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
            simp only [Algebra.smul_def, targetRing_mk_mul])).comp
              (targetModuleAddEquiv t M).toAddMonoidHom
      map_zero' := by
        ext x
        rcases x with ⟨x⟩
        induction x with
        | tmul c' m =>
          change (PairRing.mk ((0 : C) ⊗ₜ[B] TargetRing.mk c') : PairRing t) ⊗ₜ[B] m = 0
          simp
        | add x y hx hy =>
          simpa only [targetModule_mk_add, map_add, add_zero] using congrArg₂ (· + ·) hx hy
      map_add' := by
        intro c d
        ext x
        rcases x with ⟨x⟩
        induction x with
        | tmul c' m =>
          change (PairRing.mk ((c + d) ⊗ₜ[B] TargetRing.mk c') : PairRing t) ⊗ₜ[B] m = _
          simp only [TensorProduct.add_tmul, pairRing_mk_add]
          rfl
        | add x y hx hy =>
          simp only [targetModule_mk_add, map_add, AddMonoidHom.add_apply]
          rw [hx, hy]
          simp only [AddMonoidHom.add_apply] }
    (fun b c x => by
      rcases x with ⟨x⟩
      induction x with
      | tmul c' m =>
        change (PairRing.mk ((b • c) ⊗ₜ[B] TargetRing.mk c')) ⊗ₜ[B] m =
          (PairRing.mk (c ⊗ₜ[B] TargetRing.mk (t b * c'))) ⊗ₜ[B] m
        congr 2
        rw [TensorProduct.smul_tmul]
        rfl
      | add x y hx hy =>
        simpa only [targetModule_mk_add, map_add, smul_add] using congrArg₂ (· + ·) hx hy)

@[simp]
lemma pairTensorMap_tmul (c c' : C) (m : M) :
    pairTensorMap t M (c ⊗ₜ[B] TargetModule.mk (c' ⊗ₜ[B] m)) =
      (PairRing.mk (c ⊗ₜ[B] TargetRing.mk c') : PairRing t) ⊗ₜ[B] m := rfl

def pairTensorInvAux : C ⊗[B] TargetRing t →+ (M →+ C ⊗[B] TargetModule t M) :=
  liftAddHom
    { toFun := fun c =>
        { toFun := fun d =>
            { toFun := fun m => c ⊗ₜ[B] TargetModule.mk (d.val ⊗ₜ[B] m)
              map_zero' := by simp
              map_add' := by
                intro m n
                simp [TensorProduct.tmul_add] }
          map_zero' := by
            ext m
            change c ⊗ₜ[B] TargetModule.mk ((0 : C) ⊗ₜ[B] m) = 0
            simp
          map_add' := by
            intro d e
            ext m
            change c ⊗ₜ[B] TargetModule.mk ((d.val + e.val) ⊗ₜ[B] m) = _
            simp [TensorProduct.add_tmul, TensorProduct.tmul_add] }
      map_zero' := by ext d m; simp
      map_add' := by intro c d; ext e m; exact TensorProduct.add_tmul _ _ _ }
    (fun b c d => by
      ext m
      change (b • c) ⊗ₜ[B] TargetModule.mk (d.val ⊗ₜ[B] m) =
        c ⊗ₜ[B] TargetModule.mk ((t b * d.val) ⊗ₜ[B] m)
      rw [TensorProduct.smul_tmul]
      rfl)

def pairTensorInv : PairRing t ⊗[B] M →+ C ⊗[B] TargetModule t M :=
  liftAddHom
    ((pairTensorInvAux t M).comp (pairRingIso t).toAddMonoidHom)
    (fun b p m => by
      change pairTensorInvAux t M (b • p).val m =
        pairTensorInvAux t M p.val (b • m)
      rw [pairRing_smul_val]
      rcases p with ⟨p⟩
      induction p with
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        change c ⊗ₜ[B] TargetModule.mk
          (((algebraMap B C b) * d.val) ⊗ₜ[B] m) =
            c ⊗ₜ[B] TargetModule.mk (d.val ⊗ₜ[B] (b • m))
        rw [← Algebra.smul_def, TensorProduct.smul_tmul]
      | add p q hp hq =>
        simpa only [mul_add, map_add, AddMonoidHom.add_apply] using congrArg₂ (· + ·) hp hq)

@[simp]
lemma pairTensorInv_tmul (c c' : C) (m : M) :
    pairTensorInv t M ((PairRing.mk (c ⊗ₜ[B] TargetRing.mk c') : PairRing t) ⊗ₜ[B] m) =
      c ⊗ₜ[B] TargetModule.mk (c' ⊗ₜ[B] m) := rfl

lemma pairTensorInv_pairTensorMap (x : C ⊗[B] TargetModule t M) :
    pairTensorInv t M (pairTensorMap t M x) = x := by
  induction x with
  | tmul c x =>
    rcases x with ⟨x⟩
    induction x with
    | tmul d m => rfl
    | add x y hx hy =>
      simpa only [targetModule_mk_add, TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) hx hy
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

lemma pairTensorMap_injective : Function.Injective (pairTensorMap t M) :=
  Function.LeftInverse.injective (pairTensorInv_pairTensorMap t M)

end GroupoidCoaction

end Langlands.AlgebraicGeometry
