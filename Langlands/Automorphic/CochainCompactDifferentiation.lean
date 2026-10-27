import Langlands.Automorphic.OperatorCompactDifferentiation
import Langlands.Global.ArchimedeanAdjointDifferentiation
import Langlands.Representation.HorizontalAlternating
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Infinitesimal compact equivariance of actual automorphic cochains -/

noncomputable section
universe u v

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] (n : ℕ)

/-- The actual ambient complex adjoint representation of the full compact group. -/
def complexCompactRepresentation :
    Representation ℂ (standardInfiniteCompact F n) (ComplexLieAlgebra F n) where
  toFun k := (complexLieConjugation F n k.val).toLinearEquiv.toLinearMap
  map_one' := by
    ext X
    simp
  map_mul' k l := by
    apply LinearMap.ext
    intro X
    exact congrArg (fun e => e X) (complexLieConjugation_mul F n k.val l.val)

@[simp]
theorem complexCompactRepresentation_apply (k : standardInfiniteCompact F n)
    (X : ComplexLieAlgebra F n) :
    complexCompactRepresentation F n k X = complexLieConjugation F n k.val X := rfl

private theorem complexMultilinear_ext
    {V : Type v} [AddCommGroup V] [Module ℂ V] (q : ℕ)
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

private def cochainInsertion
    {V : Type v} [AddCommGroup V] [Module ℂ V] (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (D : Module.End ℂ (ComplexLieAlgebra F n)) :
    MultilinearMap ℂ (fun _ : Fin q => ComplexLieAlgebra F n) V :=
  ∑ i : Fin q, f.toMultilinearMap.compLinearMap
    (Function.update (fun _ => LinearMap.id) i D)

private theorem cochainInsertion_apply
    {V : Type v} [AddCommGroup V] [Module ℂ V] (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (D : Module.End ℂ (ComplexLieAlgebra F n)) (X : Fin q → ComplexLieAlgebra F n) :
    cochainInsertion F n q f D X = ∑ i, f (Function.update X i (D (X i))) := by
  simp only [cochainInsertion, sum_apply, MultilinearMap.compLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  change f (fun j => Function.update (fun _ => LinearMap.id) i D j (X j)) =
    f (Function.update X i (D (X i)))
  apply congrArg f
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj, LinearMap.id_apply]

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions
open ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

private def scalarEvaluation (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    S.Space →ₗ[ℂ] ℂ where
  toFun v := evaluate F n (S.toContinuous v) (AdelicGL.pair F n a b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Scalar differentiation of full compact equivariance on complexified real tuples. -/
theorem evaluate_cochain_compact_real (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) S.compactRepresentation q)
    (Y : compactLieSubalgebra F n) (X : Fin q → RealLieAlgebra F n)
    (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    evaluate F n (S.toContinuous (S.complexLieAction (complexify F n Y.val)
      (f (fun i => complexify F n (X i))))) (AdelicGL.pair F n a b) =
    evaluate F n (S.toContinuous (∑ i, f (Function.update
      (fun j => complexify F n (X j)) i (complexify F n ⁅Y.val, X i⁆))))
        (AdelicGL.pair F n a b) := by
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n Y
  have hd := S.compactCurve_evaluate_deriv Y.val c hc0 hc
    (f (fun i => complexify F n (X i))) a b
  have he := compactCurve_scalarCochain_deriv F n q f (S.scalarEvaluation a b)
    Y X c hc0 hc
  have hcurve :
      (fun t => S.scalarEvaluation a b
        (f (fun i => complexify F n (realLieConjugation F n (c t).val (X i))))) =
      (fun t => evaluate F n (S.toContinuous (S.compactRepresentation (c t)
        (f (fun i => complexify F n (X i))))) (AdelicGL.pair F n a b)) := by
    funext t
    change S.scalarEvaluation a b
      (f (fun i => complexify F n (realLieConjugation F n (c t).val (X i)))) =
      S.scalarEvaluation a b (S.compactRepresentation (c t)
        (f (fun i => complexify F n (X i))))
    have hh := hf (c t) (fun i => complexify F n (X i))
    simpa only [complexCompactRepresentation_apply,
      complexLieConjugation_complexify] using congrArg (S.scalarEvaluation a b) hh
  rw [hcurve] at he
  have hu := hd.unique he
  rw [← map_sum] at hu
  change _ = evaluate F n (S.toContinuous (∑ i, f (Function.update
    (fun j => complexify F n (X j)) i (complexify F n ⁅Y.val, X i⁆))))
      (AdelicGL.pair F n a b) at hu
  exact hu

/-- Actual full compact equivariance implies the real infinitesimal insertion identity. -/
theorem cochain_compact_real (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) S.compactRepresentation q)
    (Y : compactLieSubalgebra F n) (X : Fin q → RealLieAlgebra F n) :
    S.complexLieAction (complexify F n Y.val) (f (fun i => complexify F n (X i))) =
      ∑ i, f (Function.update (fun j => complexify F n (X j)) i
        (complexify F n ⁅Y.val, X i⁆)) := by
  apply S.toContinuous_injective
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate F n (S.toContinuous
    (S.complexLieAction (complexify F n Y.val) (f (fun i => complexify F n (X i))))) x =
    evaluate F n (S.toContinuous (∑ i, f (Function.update
      (fun j => complexify F n (X j)) i (complexify F n ⁅Y.val, X i⁆)))) x
  have h := S.evaluate_cochain_compact_real q f hf Y X
    (AdelicGL.infinite F n x) (AdelicGL.finite F n x)
  simpa only [AdelicGL.pair_projections] using h

/-- The real compact insertion identity on arbitrary complex Lie input tuples. -/
theorem cochain_compact_real_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) S.compactRepresentation q)
    (Y : compactLieSubalgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    S.complexLieAction (complexify F n Y.val) (f X) =
      ∑ i, f (Function.update X i ⁅complexify F n Y.val, X i⁆) := by
  let D := LieAlgebra.ad ℂ (ComplexLieAlgebra F n) (complexify F n Y.val)
  have hm :
      (S.complexLieAction (complexify F n Y.val)).compMultilinearMap f.toMultilinearMap =
        cochainInsertion F n q f D := by
    apply complexMultilinear_ext F n q
    intro xs
    rw [LinearMap.compMultilinearMap_apply, cochainInsertion_apply]
    change S.complexLieAction (complexify F n Y.val)
      (f (fun i => complexify F n (xs i))) =
        ∑ i, f (Function.update (fun j => complexify F n (xs j)) i
          ⁅complexify F n Y.val, complexify F n (xs i)⁆)
    simp only [← (complexify F n).map_lie]
    exact S.cochain_compact_real q f hf Y xs
  have h := congrArg (fun A : MultilinearMap ℂ
    (fun _ : Fin q => ComplexLieAlgebra F n) S.Space => A X) hm
  simpa only [LinearMap.compMultilinearMap_apply, cochainInsertion_apply,
    D, LieAlgebra.ad_apply, AlternatingMap.coe_multilinearMap] using h

/-- Full compact equivariance implies actual complex infinitesimal equivariance
in every degree, by differentiation and scalar extension. -/
theorem cochain_compact_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) S.compactRepresentation q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    S.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆) := by
  induction Y using TensorProduct.inductionOn with
  | tmul z Y =>
    rw [compactLieAction_apply, compactComplexInclusion_tmul]
    have ht : z ⊗ₜ[ℝ] Y.val = z • complexify F n Y.val := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, LinearMap.smul_apply, S.cochain_compact_real_complex q f hf Y X]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.smul_lie z (complexify F n Y.val) (X i)]
    exact (f.map_update_smul X i z ⁅complexify F n Y.val, X i⁆).symm
  | add Y Z hY hZ =>
    simp only [map_add, LinearMap.add_apply, add_lie, f.map_update_add,
      Finset.sum_add_distrib, hY, hZ]

/-- Actual cochains satisfying the complex compact infinitesimal insertion identity. -/
def infinitesimalCompactCochains (q : ℕ) :
    Submodule ℂ ((ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space) where
  carrier := {f | ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n),
    S.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆)}
  zero_mem' := by
    intro Y X
    simp
  add_mem' hf hg := by
    intro Y X
    simpa only [AlternatingMap.add_apply, map_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hf Y X) (hg Y X)
  smul_mem' z f hf := by
    intro Y X
    simpa only [AlternatingMap.smul_apply, map_smul, Finset.smul_sum] using
      congrArg (fun v : S.Space => z • v) (hf Y X)

@[simp]
theorem mem_infinitesimalCompactCochains (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space) :
    f ∈ S.infinitesimalCompactCochains q ↔
      ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n),
        S.compactLieAction Y (f X) =
          ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆) := Iff.rfl

/-- Identity inclusion with infinitesimal membership derived from actual full
compact equivariance, rather than supplied as a compatibility certificate. -/
def compactEquivariantLieInclusion (q : ℕ) :
    HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) S.compactRepresentation q →ₗ[ℂ]
        S.infinitesimalCompactCochains q where
  toFun f := ⟨f.val, S.cochain_compact_complex q f.val f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem compactEquivariantLieInclusion_coe (q : ℕ)
    (f : HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) S.compactRepresentation q) :
    (S.compactEquivariantLieInclusion q f).val = f.val := rfl

theorem compactEquivariantLieInclusion_injective (q : ℕ) :
    Function.Injective (S.compactEquivariantLieInclusion q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : S.infinitesimalCompactCochains q => v.val) h)

end OperatorRealization
end Langlands.Automorphic
