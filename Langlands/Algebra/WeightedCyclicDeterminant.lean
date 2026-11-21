import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.OfFn

/-! # Determinant of a weighted cyclic shift -/

namespace Langlands.Algebra

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- Subtract the weighted cyclic shift from the identity on a product of copies of `V`. -/
def weightedCycleDefect {d : ℕ} (A : Fin d → Module.End K V) :
    Module.End K (Fin d → V) where
  toFun x i := x i - A i (x (finRotate d i))
  map_add' x y := by
    funext i
    simp [add_sub_add_comm]
  map_smul' c x := by
    funext i
    simp [smul_sub]

@[simp]
theorem weightedCycleDefect_apply {d : ℕ} (A : Fin d → Module.End K V)
    (x : Fin d → V) (i : Fin d) : weightedCycleDefect A x i = x i - A i (x (finRotate d i)) :=
  rfl

private def splitLast (n : ℕ) : (Fin (n + 1) → V) ≃ₗ[K] (Fin n → V) × V where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun x := Fin.snoc x.1 x.2
  left_inv x := Fin.snoc_init_self x
  right_inv x := by
    apply Prod.ext
    · exact @Fin.init_snoc n (fun _ => V) x.2 x.1
    · exact @Fin.snoc_last n (fun _ => V) x.2 x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def upperBlock (a : Module.End K V) (b : W →ₗ[K] V) (d : Module.End K W) :
    Module.End K (V × W) :=
  ((a.comp (LinearMap.fst K V W)) + b.comp (LinearMap.snd K V W)).prod
    (d.comp (LinearMap.snd K V W))

private def lowerBlock (a : Module.End K V) (c : V →ₗ[K] W) (d : Module.End K W) :
    Module.End K (V × W) :=
  (a.comp (LinearMap.fst K V W)).prod
    ((c.comp (LinearMap.fst K V W)) + d.comp (LinearMap.snd K V W))

private theorem det_upperBlock [FiniteDimensional K V] [FiniteDimensional K W]
    (a : Module.End K V) (b : W →ₗ[K] V) (d : Module.End K W) :
    (upperBlock a b d).det = a.det * d.det := by
  classical
  let v := Module.finBasis K V
  let w := Module.finBasis K W
  have hm : LinearMap.toMatrix (v.prod w) (v.prod w) (upperBlock a b d) =
      Matrix.fromBlocks (LinearMap.toMatrix v v a) (LinearMap.toMatrix w v b) 0
        (LinearMap.toMatrix w w d) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply', upperBlock]
  rw [← LinearMap.det_toMatrix (v.prod w), hm, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

private theorem det_lowerBlock [FiniteDimensional K V] [FiniteDimensional K W]
    (a : Module.End K V) (c : V →ₗ[K] W) (d : Module.End K W) :
    (lowerBlock a c d).det = a.det * d.det := by
  let e := LinearEquiv.prodComm K V W
  have he : (e : V × W →ₗ[K] W × V).comp ((lowerBlock a c d).comp e.symm.toLinearMap) =
      upperBlock d c a := by
    ext p <;> simp [e, lowerBlock, upperBlock, add_comm]
  rw [← LinearMap.det_conj _ e, he, det_upperBlock, mul_comm]

/-- The determinant on the product is the determinant of the defect of the ordered
product `A 0 * A 1 * ⋯ * A (Fin.last d)` on one copy of the space. -/
theorem det_weightedCycleDefect [FiniteDimensional K V] {d : ℕ}
    (A : Fin (d + 1) → Module.End K V) :
    (weightedCycleDefect A).det = LinearMap.det (1 - (List.ofFn A).prod) := by
  induction d with
  | zero =>
    let e := LinearEquiv.funUnique (Fin 1) K V
    have he : (e : (Fin 1 → V) →ₗ[K] V).comp ((weightedCycleDefect A).comp e.symm.toLinearMap) =
        1 - A 0 := by
      ext x
      change weightedCycleDefect A (fun _ => x) 0 = x - A 0 x
      rw [weightedCycleDefect_apply]
    rw [← LinearMap.det_conj _ e, he, List.ofFn_succ, List.ofFn_zero, List.prod_singleton]
  | succ d ih =>
    let A' : Fin (d + 1) → Module.End K V :=
      Fin.snoc (fun i : Fin d => A i.castSucc.castSucc)
        (A (Fin.last d).castSucc * A (Fin.last (d + 1)))
    have hp : (List.ofFn A').prod = (List.ofFn A).prod := by
      simp only [List.ofFn_succ', List.prod_concat, A', Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]
    let e := splitLast (K := K) (V := V) (d + 1)
    let D := e.toLinearMap.comp ((weightedCycleDefect A).comp e.symm.toLinearMap)
    let f : (Fin (d + 1) → V) →ₗ[K] V := (A (Fin.last (d + 1))).comp (LinearMap.proj 0)
    let g : V →ₗ[K] (Fin (d + 1) → V) :=
      LinearMap.pi fun i => if i = Fin.last d then -(A (Fin.last d).castSucc) else 0
    have hstep : D.comp (lowerBlock LinearMap.id f LinearMap.id) =
        upperBlock (weightedCycleDefect A') g LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change (let z := Fin.snoc x (A (Fin.last (d + 1)) (x 0) + y);
        ((fun i => weightedCycleDefect A z i.castSucc), weightedCycleDefect A z (Fin.last (d + 1)))) =
        (weightedCycleDefect A' x + g y, y)
      dsimp only
      apply Prod.ext
      · funext i
        change weightedCycleDefect A (Fin.snoc x (A (Fin.last (d + 1)) (x 0) + y)) i.castSucc =
          weightedCycleDefect A' x i + (if i = Fin.last d then -(A (Fin.last d).castSucc) else 0) y
        rw [weightedCycleDefect_apply, weightedCycleDefect_apply, Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have hr : finRotate (d + 2) (Fin.last d).castSucc = Fin.last (d + 1) := by
            apply Fin.ext
            rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last _)]
            rfl
          rw [ite_eq_left rfl, finRotate_last, hr, Fin.snoc_last]
          simp only [A', Fin.snoc_last, Module.End.mul_apply, LinearMap.neg_apply, map_add]
          abel
        · have hr : finRotate (d + 2) j.castSucc.castSucc =
              (finRotate (d + 1) j.castSucc).castSucc := by
            apply Fin.ext
            simp only [Fin.val_castSucc, coe_finRotate_of_ne_last (Fin.castSucc_ne_last _)]
          rw [hr, Fin.snoc_castSucc]
          simp [A', Fin.castSucc_ne_last]
      · simp [Fin.snoc_apply_zero]
    have hd := congrArg (fun L : Module.End K ((Fin (d + 1) → V) × V) => L.det) hstep
    simp only [LinearMap.det_comp, det_lowerBlock, det_upperBlock, LinearMap.det_id,
      mul_one] at hd
    change LinearMap.det (e.toLinearMap.comp ((weightedCycleDefect A).comp e.symm.toLinearMap)) = _ at hd
    rw [LinearMap.det_conj] at hd
    rw [hd, ih, hp]

end Langlands.Algebra
