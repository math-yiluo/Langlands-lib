import Langlands.Algebra.UniversalEnvelopingSymmetrization
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! # Symmetrization from the whole symmetric algebra -/

noncomputable section
universe v
set_option autoImplicit false
open scoped TensorProduct DirectSum BigOperators

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]

local notation "T" => TensorAlgebra R L
local notation "U" => UniversalEnvelopingAlgebra R L

/-- Symmetrize each homogeneous tensor component and sum the results. -/
def tensorSymmetrize : T →ₗ[R] U :=
  (DirectSum.toModule R ℕ U (fun d => PiTensorProduct.lift (symmetricWord R L d))).comp
    TensorAlgebra.toDirectSum.toLinearMap

@[simp] theorem tensorSymmetrize_tprod {d : ℕ} (x : Fin d → L) :
    tensorSymmetrize R L (TensorAlgebra.tprod R L d x) = symmetricWord R L d x := by
  simp only [tensorSymmetrize, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod]
  change (DirectSum.toModule R ℕ U (fun d => PiTensorProduct.lift (symmetricWord R L d)))
    (DirectSum.lof R ℕ (fun d => ⨂[R]^d L) d (PiTensorProduct.tprod R x)) = _
  rw [DirectSum.toModule_lof, PiTensorProduct.lift.tprod]

/-- Ordered products of the tensor-algebra generators. -/
def tensorWord (l : List L) : T := (l.map (TensorAlgebra.ι R)).prod

@[simp] theorem tensorWord_append (l r : List L) :
    tensorWord R L (l ++ r) = tensorWord R L l * tensorWord R L r := by
  simp [tensorWord]

@[simp] theorem tensorWord_cons (x : L) (l : List L) :
    tensorWord R L (x :: l) = TensorAlgebra.ι R x * tensorWord R L l := rfl

@[simp] theorem tensorWord_nil : tensorWord R L [] = 1 := rfl

theorem tensorWord_eq_tprod (l : List L) :
    tensorWord R L l = TensorAlgebra.tprod R L l.length l.get := by
  simp only [TensorAlgebra.tprod_apply, List.ofFn_comp', List.ofFn_get, tensorWord]

@[simp] theorem tensorSymmetrize_word (l : List L) :
    tensorSymmetrize R L (tensorWord R L l) = symmetricWord R L l.length l.get := by
  rw [tensorWord_eq_tprod, tensorSymmetrize_tprod]

/-- Linear maps on the tensor algebra are determined by generator words. -/
theorem tensor_linearMap_ext {N : Type*} [AddCommGroup N] [Module R N]
    {f g : T →ₗ[R] N}
    (h : ∀ (l : List L), f (tensorWord R L l) = g (tensorWord R L l)) : f = g := by
  have heq : f.comp TensorAlgebra.ofDirectSum.toLinearMap =
      g.comp TensorAlgebra.ofDirectSum.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro d
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      DirectSum.lof_eq_of, AlgHom.toLinearMap_apply, TensorAlgebra.ofDirectSum_of_tprod,
      TensorAlgebra.tprod_apply, List.map_ofFn, Function.comp_def, tensorWord] using
      h (List.ofFn x)
  ext a
  have hh := LinearMap.congr_fun heq (TensorAlgebra.toDirectSum a)
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.ofDirectSum_toDirectSum] using hh

omit [LieRing L] in
/-- The two marked positions can be swapped without moving either context. -/
private theorem append_cons_swap {m n : ℕ} (l : Fin m → L) (r : Fin n → L) (x y : L) :
    Fin.append l (Fin.cons x (Fin.cons y r)) ∘
      Equiv.swap ((0 : Fin (n + 2)).natAdd m)
        (((0 : Fin (n + 1)).succ).natAdd m) =
      Fin.append l (Fin.cons y (Fin.cons x r)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h0 : j.castAdd (n + 2) ≠ (0 : Fin (n + 2)).natAdd m := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, Nat.add_zero] at this
      omega
    have h1 : j.castAdd (n + 2) ≠ ((0 : Fin (n + 1)).succ).natAdd m := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ, Fin.val_zero] at this
      omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.append_left]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.append_right,
        Fin.cons_succ, Fin.cons_zero]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Function.comp_apply, Equiv.swap_apply_right, Fin.append_right,
          Fin.cons_succ, Fin.cons_zero]
      · have h0 : k.succ.succ.natAdd m ≠ (0 : Fin (n + 2)).natAdd m := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_zero] at this
          omega
        have h1 : k.succ.succ.natAdd m ≠ ((0 : Fin (n + 1)).succ).natAdd m := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_zero] at this
          omega
        simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1,
          Fin.append_right, Fin.cons_succ]

private theorem tensorWord_context_eq_tprod (l r : List L) (x y : L) :
    tensorWord R L (l ++ x :: y :: r) =
      TensorAlgebra.tprod R L (l.length + (r.length + 2))
        (Fin.append l.get (Fin.cons x (Fin.cons y r.get))) := by
  simp only [TensorAlgebra.tprod_apply, List.ofFn_comp', List.ofFn_fin_append,
    List.ofFn_cons, List.ofFn_get, tensorWord, List.map_append, List.map_cons,
    List.prod_append, List.prod_cons]

/-- Symmetrization respects an adjacent generator swap inside generator words. -/
theorem tensorSymmetrize_word_context_swap (l r : List L) (x y : L) :
    tensorSymmetrize R L (tensorWord R L (l ++ x :: y :: r)) =
      tensorSymmetrize R L (tensorWord R L (l ++ y :: x :: r)) := by
  rw [tensorWord_context_eq_tprod, tensorWord_context_eq_tprod,
    tensorSymmetrize_tprod, tensorSymmetrize_tprod]
  exact (symmetricWord_perm R L
    (Equiv.swap ((0 : Fin (r.length + 2)).natAdd l.length)
      (((0 : Fin (r.length + 1)).succ).natAdd l.length))
      (Fin.append l.get (Fin.cons x (Fin.cons y r.get)))).symm.trans
        (congrArg (symmetricWord R L _) (append_cons_swap L l.get r.get x y))

/-- Symmetrization respects a generator swap inside arbitrary tensor-algebra contexts. -/
theorem tensorSymmetrize_context_swap (c d : T) (x y : L) :
    tensorSymmetrize R L (c * (TensorAlgebra.ι R x * TensorAlgebra.ι R y) * d) =
      tensorSymmetrize R L (c * (TensorAlgebra.ι R y * TensorAlgebra.ι R x) * d) := by
  let a := TensorAlgebra.ι R x * TensorAlgebra.ι R y
  let b := TensorAlgebra.ι R y * TensorAlgebra.ι R x
  have heq : (tensorSymmetrize R L).comp
      (((LinearMap.mul R T).flip d).comp ((LinearMap.mul R T).flip a)) =
      (tensorSymmetrize R L).comp
        (((LinearMap.mul R T).flip d).comp ((LinearMap.mul R T).flip b)) := by
    apply tensor_linearMap_ext R L
    intro l
    have hinner : (tensorSymmetrize R L).comp (LinearMap.mul R T (tensorWord R L l * a)) =
        (tensorSymmetrize R L).comp (LinearMap.mul R T (tensorWord R L l * b)) := by
      apply tensor_linearMap_ext R L
      intro r
      simpa only [LinearMap.comp_apply, LinearMap.mul_apply', a, b,
        tensorWord_append, tensorWord_cons, mul_assoc] using
          tensorSymmetrize_word_context_swap R L l r x y
    exact LinearMap.congr_fun hinner d
  exact LinearMap.congr_fun heq c

/-- The full symmetric-algebra congruence is respected in every pair of contexts. -/
theorem tensorSymmetrize_context_congr {a b : T}
    (hab : TensorAlgebra.symRingCon R L a b) (c d : T) :
    tensorSymmetrize R L (c * a * d) = tensorSymmetrize R L (c * b * d) := by
  change RingConGen.Rel (TensorAlgebra.SymRel R L) a b at hab
  induction hab generalizing c d with
  | of a b h =>
    cases h with
    | mul_comm x y => exact tensorSymmetrize_context_swap R L c d x y
  | refl => rfl
  | symm h ih => exact (ih c d).symm
  | trans h h' ih ih' => exact (ih c d).trans (ih' c d)
  | add h h' ih ih' =>
    simp only [mul_add, add_mul, map_add, ih c d, ih' c d]
  | @mul w x y z h h' ih ih' =>
    calc
      tensorSymmetrize R L (c * (w * y) * d) =
          tensorSymmetrize R L (c * (x * y) * d) := by
        simpa only [mul_assoc] using ih c (y * d)
      _ = tensorSymmetrize R L (c * (x * z) * d) := by
        simpa only [mul_assoc] using ih' (c * x) d

/-- Normalized linear symmetrization from the actual whole symmetric algebra. -/
def symmetricAlgebraSymmetrize : SymmetricAlgebra R L →ₗ[R] U where
  toFun := Quotient.lift (tensorSymmetrize R L) (fun a b h => by
    simpa only [one_mul, mul_one] using tensorSymmetrize_context_congr R L h 1 1)
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b => exact (tensorSymmetrize R L).map_add a b
  map_smul' := by
    intro r a
    induction a using Quotient.inductionOn with
    | _ a => exact (tensorSymmetrize R L).map_smul r a

@[simp] theorem symmetricAlgebraSymmetrize_algHom (a : T) :
    symmetricAlgebraSymmetrize R L (SymmetricAlgebra.algHom R L a) =
      tensorSymmetrize R L a := rfl

/-- Symmetrization of a symmetric-algebra monomial is the normalized ordered average. -/
theorem symmetricAlgebraSymmetrize_prod (l : List L) :
    symmetricAlgebraSymmetrize R L ((l.map (SymmetricAlgebra.ι R L)).prod) =
      symmetricWord R L l.length l.get := by
  have heq : SymmetricAlgebra.algHom R L (tensorWord R L l) =
      (l.map (SymmetricAlgebra.ι R L)).prod := by
    simp only [tensorWord, map_list_prod, List.map_map]
    rfl
  rw [← heq, symmetricAlgebraSymmetrize_algHom, tensorSymmetrize_word]

@[simp] theorem symmetricAlgebraSymmetrize_one :
    symmetricAlgebraSymmetrize R L 1 = 1 := by
  simpa [symmetricWord_apply, orderedWord_apply, word] using
    symmetricAlgebraSymmetrize_prod R L []

@[simp] theorem symmetricAlgebraSymmetrize_ι (x : L) :
    symmetricAlgebraSymmetrize R L (SymmetricAlgebra.ι R L x) =
      UniversalEnvelopingAlgebra.ι R x := by
  simpa [symmetricWord_apply, orderedWord_apply, word] using
    symmetricAlgebraSymmetrize_prod R L [x]

@[simp] theorem symmetricAlgebraSymmetrize_algebraMap (r : R) :
    symmetricAlgebraSymmetrize R L (algebraMap R (SymmetricAlgebra R L) r) =
      algebraMap R U r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, symmetricAlgebraSymmetrize_one,
    Algebra.algebraMap_eq_smul_one]

/-- A homogeneous monomial has symmetrization in the corresponding degree bound. -/
theorem symmetricAlgebraSymmetrize_prod_mem (l : List L) :
    symmetricAlgebraSymmetrize R L ((l.map (SymmetricAlgebra.ι R L)).prod) ∈
      degreeFiltration R L l.length := by
  rw [symmetricAlgebraSymmetrize_prod]
  exact symmetricWord_mem_degreeFiltration R L l.get

/-- Linear maps out of the tensor algebra agree if they agree on all pure words. -/
theorem tensor_linearMap_ext_tprod {N : Type*} [AddCommGroup N] [Module R N]
    {f g : T →ₗ[R] N}
    (h : ∀ (d : ℕ) (x : Fin d → L),
      f (TensorAlgebra.tprod R L d x) = g (TensorAlgebra.tprod R L d x)) : f = g := by
  apply tensor_linearMap_ext R L
  intro l
  rw [tensorWord_eq_tprod]
  exact h l.length l.get

private theorem tensor_map_tprod {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (h : L →ₗ[R] L') {d : ℕ} (x : Fin d → L) :
    TensorAlgebra.lift R ((TensorAlgebra.ι R).comp h) (TensorAlgebra.tprod R L d x) =
      TensorAlgebra.tprod R L' d (fun i => h (x i)) := by
  simp only [TensorAlgebra.tprod_apply, map_list_prod, List.map_ofFn,
    Function.comp_def, TensorAlgebra.lift_ι_apply, LinearMap.comp_apply]

/-- Total tensor symmetrization is natural under compatible maps on enveloping generators. -/
theorem map_tensorSymmetrize {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : U →ₐ[R] UniversalEnvelopingAlgebra R L') (h : L →ₗ[R] L')
    (hgen : ∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (h x)) (a : T) :
    f (tensorSymmetrize R L a) = tensorSymmetrize R L'
      (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp h) a) := by
  have heq : f.toLinearMap.comp (tensorSymmetrize R L) =
      (tensorSymmetrize R L').comp
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp h)).toLinearMap := by
    apply tensor_linearMap_ext_tprod R L
    intro d x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, tensor_map_tprod,
      tensorSymmetrize_tprod]
    exact map_symmetricWord R L f h hgen x
  exact LinearMap.congr_fun heq a

/-- Whole symmetric-algebra symmetrization is natural under compatible generator maps. -/
theorem map_symmetricAlgebraSymmetrize {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : U →ₐ[R] UniversalEnvelopingAlgebra R L') (h : L →ₗ[R] L')
    (hgen : ∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (h x)) (a : SymmetricAlgebra R L) :
    f (symmetricAlgebraSymmetrize R L a) = symmetricAlgebraSymmetrize R L'
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L').comp h) a) := by
  obtain ⟨b, rfl⟩ := SymmetricAlgebra.algHom_surjective R L a
  have hcomm : (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L').comp h)).comp
      (SymmetricAlgebra.algHom R L) =
      (SymmetricAlgebra.algHom R L').comp
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp h)) := by
    apply TensorAlgebra.hom_ext
    ext x
    change SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L').comp h)
      (SymmetricAlgebra.ι R L x) = _
    simp only [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply, TensorAlgebra.lift_ι_apply]
    rfl
  rw [show SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L').comp h)
      (SymmetricAlgebra.algHom R L b) = SymmetricAlgebra.algHom R L'
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp h) b) from AlgHom.congr_fun hcomm b,
    symmetricAlgebraSymmetrize_algHom, symmetricAlgebraSymmetrize_algHom]
  exact map_tensorSymmetrize R L f h hgen b

/-- In characteristic zero the monomial comparison has a strict degree drop. -/
theorem symmetricAlgebraSymmetrize_prod_sub_word_mem [CharZero R] (l : List L) :
    symmetricAlgebraSymmetrize R L ((l.map (SymmetricAlgebra.ι R L)).prod) -
      word R L l ∈ degreeFiltration R L (l.length - 1) := by
  rw [symmetricAlgebraSymmetrize_prod]
  simpa only [orderedWord_apply, List.ofFn_get] using
    symmetricWord_sub_orderedWord_mem R L l.get

end Langlands.Algebra.UniversalEnveloping
