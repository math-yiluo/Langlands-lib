import Langlands.Global.ArchimedeanAdjointDifferentiation
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Scalar extension of actual cochain insertion identities -/

noncomputable section

universe u v

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] (n : ℕ)
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Complex multilinear maps on the actual complexified Lie algebra are
determined by their values on tuples of actual real Lie vectors. -/
theorem complexMultilinear_ext_on_real (q : ℕ)
    (f g : MultilinearMap ℂ (fun _ : Fin q => ComplexLieAlgebra F n) V)
    (h : ∀ X : Fin q → RealLieAlgebra F n,
      f (fun i => complexify F n (X i)) = g (fun i => complexify F n (X i))) :
    f = g := by
  induction q with
  | zero =>
    ext X
    have hx : X = (fun i : Fin 0 => complexify F n (Fin.elim0 i)) :=
      Subsingleton.elim _ _
    rw [hx]
    exact h (fun i => Fin.elim0 i)
  | succ q ih =>
    have hc : f.curryLeft = g.curryLeft := by
      apply LinearMap.ext
      intro Z
      induction Z using TensorProduct.inductionOn with
      | tmul z X =>
        have hr : f.curryLeft (complexify F n X) = g.curryLeft (complexify F n X) := by
          apply ih
          intro xs
          have he : (fun i : Fin (q + 1) => complexify F n
              (Fin.cons (α := fun _ => RealLieAlgebra F n) X xs i)) =
              Fin.cons (α := fun _ => ComplexLieAlgebra F n)
                (complexify F n X) (fun i => complexify F n (xs i)) := by
            funext i
            cases i using Fin.cases <;> rfl
          simpa only [MultilinearMap.curryLeft_apply, he] using h (Fin.cons X xs)
        have ht : z ⊗ₜ[ℝ] X = z • complexify F n X := by
          simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [ht, map_smul, map_smul, hr]
      | add X Y hX hY =>
        rw [map_add, map_add, hX, hY]
    apply MultilinearMap.ext
    intro X
    have hx := congrArg (fun L : ComplexLieAlgebra F n →ₗ[ℂ]
      MultilinearMap ℂ (fun _ : Fin q => ComplexLieAlgebra F n) V =>
        L (X 0) (Fin.tail X)) hc
    simpa only [MultilinearMap.curryLeft_apply, Fin.cons_self_tail] using hx

/-- The multilinear sum inserting a fixed linear operator in every argument. -/
def complexCochainInsertion (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (D : Module.End ℂ (ComplexLieAlgebra F n)) :
    MultilinearMap ℂ (fun _ : Fin q => ComplexLieAlgebra F n) V :=
  ∑ i : Fin q, f.toMultilinearMap.compLinearMap
    (Function.update (fun _ => LinearMap.id) i D)

@[simp]
theorem complexCochainInsertion_apply (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (D : Module.End ℂ (ComplexLieAlgebra F n)) (X : Fin q → ComplexLieAlgebra F n) :
    complexCochainInsertion F n q f D X = ∑ i, f (Function.update X i (D (X i))) := by
  simp only [complexCochainInsertion, sum_apply, MultilinearMap.compLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg f
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj, LinearMap.id_apply]

/-- An insertion identity on actual real tuples extends to all complex tuples.
The premise is an equality to prove, with no topological or group assumption. -/
theorem complexCochainInsertion_of_real (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (T : Module.End ℂ V) (Y : RealLieAlgebra F n)
    (h : ∀ X : Fin q → RealLieAlgebra F n,
      T (f (fun i => complexify F n (X i))) =
        ∑ i, f (Function.update (fun j => complexify F n (X j)) i
          (complexify F n ⁅Y, X i⁆)))
    (X : Fin q → ComplexLieAlgebra F n) :
    T (f X) = ∑ i, f (Function.update X i ⁅complexify F n Y, X i⁆) := by
  let D := LieAlgebra.ad ℂ (ComplexLieAlgebra F n) (complexify F n Y)
  have hm : T.compMultilinearMap f.toMultilinearMap = complexCochainInsertion F n q f D := by
    apply complexMultilinear_ext_on_real F n q
    intro xs
    rw [LinearMap.compMultilinearMap_apply, complexCochainInsertion_apply]
    change T (f (fun i => complexify F n (xs i))) =
      ∑ i, f (Function.update (fun j => complexify F n (xs j)) i
        ⁅complexify F n Y, complexify F n (xs i)⁆)
    simp only [← (complexify F n).map_lie]
    exact h xs
  have he := congrArg (fun A : MultilinearMap ℂ
    (fun _ : Fin q => ComplexLieAlgebra F n) V => A X) hm
  simpa only [LinearMap.compMultilinearMap_apply, complexCochainInsertion_apply,
    D, LieAlgebra.ad_apply, AlternatingMap.coe_multilinearMap] using he

end Langlands.Global.ArchimedeanGL
