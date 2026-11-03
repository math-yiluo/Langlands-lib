import Langlands.RingTheory.Coalgebra.ConvolutionBaseChange

/-!
# Checks for scalar extension of finite convolution duals

Internal interface, structure and boundary checks for
`Langlands.CoalgebraDescent.convolutionDualBaseChangeEquiv`. See the same-stem
Markdown for their scope.
-/

set_option autoImplicit false
-- The types of complete polymorphic interfaces intentionally take maxima.
set_option linter.checkUnivs false

noncomputable section

open TensorProduct WithConv
open scoped Coalgebra

namespace Langlands.CoalgebraDescent.ConvolutionBaseChangeChecks

universe u v w x

/-! ### Complete interfaces -/

private abbrev LinearEquivInterface :=
  (k : Type u) → [Field k] → (D : Type v) → [AddCommGroup D] → [Module k D] →
  (K : Type w) → [Field K] → [Algebra k K] → [FiniteDimensional k D] →
  K ⊗[k] WithConv (D →ₗ[k] k) ≃ₗ[K] WithConv ((K ⊗[k] D) →ₗ[K] K)

example : LinearEquivInterface.{u,v,w} := @convolutionDualBaseChangeLinearEquiv.{u,v,w}
example : LinearEquivInterface.{0,1,2} := @convolutionDualBaseChangeLinearEquiv.{0,1,2}
example : LinearEquivInterface.{2,1,0} := @convolutionDualBaseChangeLinearEquiv.{2,1,0}

private abbrev LinearEquivTmulApplyInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    (a b : K) (f : WithConv (D →ₗ[k] k)) (d : D),
    convolutionDualBaseChangeLinearEquiv k D K (a ⊗ₜ[k] f) (b ⊗ₜ[k] d) =
      a * b * algebraMap k K (f d)

example : LinearEquivTmulApplyInterface.{u,v,w} :=
  @convolutionDualBaseChangeLinearEquiv_tmul_apply.{u,v,w}
example : LinearEquivTmulApplyInterface.{0,1,2} :=
  @convolutionDualBaseChangeLinearEquiv_tmul_apply.{0,1,2}
example : LinearEquivTmulApplyInterface.{2,1,0} :=
  @convolutionDualBaseChangeLinearEquiv_tmul_apply.{2,1,0}

private abbrev EquivInterface :=
  (k : Type u) → [Field k] → (D : Type v) → [AddCommGroup D] → [Module k D] →
  [Coalgebra k D] → (K : Type w) → [Field K] → [Algebra k K] → [FiniteDimensional k D] →
  K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K] WithConv ((K ⊗[k] D) →ₗ[K] K)

example : EquivInterface.{u,v,w} := @convolutionDualBaseChangeEquiv.{u,v,w}
example : EquivInterface.{0,1,2} := @convolutionDualBaseChangeEquiv.{0,1,2}
example : EquivInterface.{2,1,0} := @convolutionDualBaseChangeEquiv.{2,1,0}

/-- The complete unapplied main equivalence, assigned by name as the entry
declaration of this check module. -/
def equivInterface :
    (k : Type u) → [Field k] → (D : Type v) → [AddCommGroup D] → [Module k D] →
    [Coalgebra k D] → (K : Type w) → [Field K] → [Algebra k K] → [FiniteDimensional k D] →
    K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K] WithConv ((K ⊗[k] D) →ₗ[K] K) :=
  @convolutionDualBaseChangeEquiv.{u,v,w}

example : EquivInterface.{u,v,w} := @equivInterface.{u,v,w}

private abbrev ToLinearEquivInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D],
    (convolutionDualBaseChangeEquiv k D K).toLinearEquiv =
      convolutionDualBaseChangeLinearEquiv k D K

example : ToLinearEquivInterface.{u,v,w} :=
  @convolutionDualBaseChangeEquiv_toLinearEquiv.{u,v,w}
example : ToLinearEquivInterface.{0,1,2} :=
  @convolutionDualBaseChangeEquiv_toLinearEquiv.{0,1,2}
example : ToLinearEquivInterface.{2,1,0} :=
  @convolutionDualBaseChangeEquiv_toLinearEquiv.{2,1,0}

private abbrev SymmToLinearEquivInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D],
    (convolutionDualBaseChangeEquiv k D K).symm.toLinearEquiv =
      (convolutionDualBaseChangeLinearEquiv k D K).symm

example : SymmToLinearEquivInterface.{u,v,w} :=
  @convolutionDualBaseChangeEquiv_symm_toLinearEquiv.{u,v,w}
example : SymmToLinearEquivInterface.{0,1,2} :=
  @convolutionDualBaseChangeEquiv_symm_toLinearEquiv.{0,1,2}
example : SymmToLinearEquivInterface.{2,1,0} :=
  @convolutionDualBaseChangeEquiv_symm_toLinearEquiv.{2,1,0}

private abbrev ApplyInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    (x : K ⊗[k] WithConv (D →ₗ[k] k)),
    convolutionDualBaseChangeEquiv k D K x = convolutionDualBaseChangeLinearEquiv k D K x

example : ApplyInterface.{u,v,w} := @convolutionDualBaseChangeEquiv_apply.{u,v,w}
example : ApplyInterface.{0,1,2} := @convolutionDualBaseChangeEquiv_apply.{0,1,2}
example : ApplyInterface.{2,1,0} := @convolutionDualBaseChangeEquiv_apply.{2,1,0}

private abbrev SymmApplyInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    (f : WithConv ((K ⊗[k] D) →ₗ[K] K)),
    (convolutionDualBaseChangeEquiv k D K).symm f =
      (convolutionDualBaseChangeLinearEquiv k D K).symm f

example : SymmApplyInterface.{u,v,w} := @convolutionDualBaseChangeEquiv_symm_apply.{u,v,w}
example : SymmApplyInterface.{0,1,2} := @convolutionDualBaseChangeEquiv_symm_apply.{0,1,2}
example : SymmApplyInterface.{2,1,0} := @convolutionDualBaseChangeEquiv_symm_apply.{2,1,0}

private abbrev TmulApplyInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    (a b : K) (f : WithConv (D →ₗ[k] k)) (d : D),
    convolutionDualBaseChangeEquiv k D K (a ⊗ₜ[k] f) (b ⊗ₜ[k] d) =
      a * b * algebraMap k K (f d)

example : TmulApplyInterface.{u,v,w} := @convolutionDualBaseChangeEquiv_tmul_apply.{u,v,w}
example : TmulApplyInterface.{0,1,2} := @convolutionDualBaseChangeEquiv_tmul_apply.{0,1,2}
example : TmulApplyInterface.{2,1,0} := @convolutionDualBaseChangeEquiv_tmul_apply.{2,1,0}

private abbrev ApplySymmApplyInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    (f : WithConv ((K ⊗[k] D) →ₗ[K] K)) (b : K) (d : D),
    convolutionDualBaseChangeEquiv k D K
        ((convolutionDualBaseChangeEquiv k D K).symm f) (b ⊗ₜ[k] d) =
      f (b ⊗ₜ[k] d)

example : ApplySymmApplyInterface.{u,v,w} :=
  @convolutionDualBaseChangeEquiv_apply_symm_apply.{u,v,w}
example : ApplySymmApplyInterface.{0,1,2} :=
  @convolutionDualBaseChangeEquiv_apply_symm_apply.{0,1,2}
example : ApplySymmApplyInterface.{2,1,0} :=
  @convolutionDualBaseChangeEquiv_apply_symm_apply.{2,1,0}

private abbrev SymmApplyApplyInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    (x : K ⊗[k] WithConv (D →ₗ[k] k)),
    (convolutionDualBaseChangeEquiv k D K).symm (convolutionDualBaseChangeEquiv k D K x) = x

example : SymmApplyApplyInterface.{u,v,w} :=
  @convolutionDualBaseChangeEquiv_symm_apply_apply.{u,v,w}
example : SymmApplyApplyInterface.{0,1,2} :=
  @convolutionDualBaseChangeEquiv_symm_apply_apply.{0,1,2}
example : SymmApplyApplyInterface.{2,1,0} :=
  @convolutionDualBaseChangeEquiv_symm_apply_apply.{2,1,0}

private abbrev SymmApplyEqSumInterface : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
    (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]
    {ι : Type x} [Fintype ι] (basis : Module.Basis ι k D)
    (f : WithConv ((K ⊗[k] D) →ₗ[K] K)),
    (convolutionDualBaseChangeEquiv k D K).symm f =
      ∑ i, f (1 ⊗ₜ[k] basis i) ⊗ₜ[k] toConv (basis.coord i)

example : SymmApplyEqSumInterface.{u,v,w,x} :=
  @convolutionDualBaseChangeEquiv_symm_apply_eq_sum.{u,v,w,x}
example : SymmApplyEqSumInterface.{0,1,2,3} :=
  @convolutionDualBaseChangeEquiv_symm_apply_eq_sum.{0,1,2,3}
example : SymmApplyEqSumInterface.{3,2,1,0} :=
  @convolutionDualBaseChangeEquiv_symm_apply_eq_sum.{3,2,1,0}

/-! ### Actual Mathlib structures -/

section Instances

variable (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
  (K : Type w) [Field K] [Algebra k K]

example : (inferInstance : Coalgebra K (K ⊗[k] D)) = TensorProduct.instCoalgebra := rfl

example : (inferInstance : Algebra K (K ⊗[k] WithConv (D →ₗ[k] k))) =
    Algebra.TensorProduct.leftAlgebra := rfl

example : (inferInstance : Algebra k (WithConv (D →ₗ[k] k))) = LinearMap.convAlgebra := rfl

example : (inferInstance : Mul (WithConv (D →ₗ[k] k))) = LinearMap.convMul := rfl

example : (inferInstance : One (WithConv (D →ₗ[k] k))) = LinearMap.convOne := rfl

example : (inferInstance : Algebra K (WithConv ((K ⊗[k] D) →ₗ[K] K))) =
    LinearMap.convAlgebra := rfl

example : (inferInstance : Semiring (WithConv ((K ⊗[k] D) →ₗ[K] K))) =
    LinearMap.convSemiring := rfl

example : (inferInstance : Mul (WithConv ((K ⊗[k] D) →ₗ[K] K))) = LinearMap.convMul := rfl

example : (inferInstance : One (WithConv ((K ⊗[k] D) →ₗ[K] K))) = LinearMap.convOne := rfl

/-- The target product is the convolution for the scalar-extended comultiplication. -/
example (F G : WithConv ((K ⊗[k] D) →ₗ[K] K)) (c : K ⊗[k] D) :
    (F * G) c =
      LinearMap.mul' K K (TensorProduct.map F.ofConv G.ofConv (Coalgebra.comul c)) :=
  LinearMap.convMul_apply F G c

/-- The target unit is the scalar-extended counit. -/
example (c : K ⊗[k] D) :
    (1 : WithConv ((K ⊗[k] D) →ₗ[K] K)) c = algebraMap K K (Coalgebra.counit c) :=
  LinearMap.convOne_apply c

example (b : K) (d : D) :
    Coalgebra.comul (R := K) (b ⊗ₜ[k] d) =
      AlgebraTensorModule.tensorTensorTensorComm k K k K K K D D
        (Coalgebra.comul b ⊗ₜ[k] Coalgebra.comul d) :=
  TensorProduct.comul_tmul b d

example (b : K) (d : D) :
    Coalgebra.counit (R := K) (b ⊗ₜ[k] d) = Coalgebra.counit (R := k) d • b :=
  TensorProduct.counit_tmul b d

/-- The equivalence preserves the actual convolution products and units. -/
example [FiniteDimensional k D] (x y : K ⊗[k] WithConv (D →ₗ[k] k)) :
    convolutionDualBaseChangeEquiv k D K (x * y) =
      convolutionDualBaseChangeEquiv k D K x * convolutionDualBaseChangeEquiv k D K y :=
  map_mul _ x y

example [FiniteDimensional k D] :
    convolutionDualBaseChangeEquiv k D K 1 = 1 :=
  map_one _

example [FiniteDimensional k D] (c : K) (x : K ⊗[k] WithConv (D →ₗ[k] k)) :
    convolutionDualBaseChangeEquiv k D K (c • x) = c • convolutionDualBaseChangeEquiv k D K x :=
  map_smul _ c x

end Instances

/-! ### Coherence of the forward and inverse formulas -/

section Coherence

variable (k : Type u) [Field k] (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
  (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k D]

/-- The inverse basis expansion applied to a forward pure-tensor image is the
dual-basis expansion of the original pure tensor. -/
example {ι : Type x} [Fintype ι] (basis : Module.Basis ι k D) (a : K)
    (f : WithConv (D →ₗ[k] k)) :
    (convolutionDualBaseChangeEquiv k D K).symm
        (convolutionDualBaseChangeEquiv k D K (a ⊗ₜ[k] f)) =
      ∑ i, (a * algebraMap k K (f (basis i))) ⊗ₜ[k] toConv (basis.coord i) := by
  rw [convolutionDualBaseChangeEquiv_symm_apply_eq_sum k D K basis]
  simp only [convolutionDualBaseChangeEquiv_tmul_apply, mul_one]

example {ι : Type x} [Fintype ι] (basis : Module.Basis ι k D) (a : K)
    (f : WithConv (D →ₗ[k] k)) :
    a ⊗ₜ[k] f =
      ∑ i, (a * algebraMap k K (f (basis i))) ⊗ₜ[k] toConv (basis.coord i) := by
  conv_lhs => rw [← convolutionDualBaseChangeEquiv_symm_apply_apply k D K (a ⊗ₜ[k] f)]
  rw [convolutionDualBaseChangeEquiv_symm_apply_eq_sum k D K basis]
  simp only [convolutionDualBaseChangeEquiv_tmul_apply, mul_one]

/-- The inverse basis expansion, mapped forward and evaluated on `b ⊗ d`,
recovers the functional's value. -/
example {ι : Type x} [Fintype ι] (basis : Module.Basis ι k D)
    (F : WithConv ((K ⊗[k] D) →ₗ[K] K)) (b : K) (d : D) :
    convolutionDualBaseChangeEquiv k D K
        (∑ i, F (1 ⊗ₜ[k] basis i) ⊗ₜ[k] toConv (basis.coord i)) (b ⊗ₜ[k] d) =
      F (b ⊗ₜ[k] d) := by
  rw [← convolutionDualBaseChangeEquiv_symm_apply_eq_sum k D K basis,
    convolutionDualBaseChangeEquiv_apply_symm_apply]

end Coherence

/-! ### Zero coalgebras -/

section Zero

variable (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]

/-- For a zero underlying module, both sides are zero algebras. -/
example (D : Type v) [AddCommGroup D] [Module k D] [Subsingleton D] :
    Unique (K ⊗[k] WithConv (D →ₗ[k] k)) := inferInstance

example (D : Type v) [AddCommGroup D] [Module k D] [Subsingleton D] :
    Unique (WithConv ((K ⊗[k] D) →ₗ[K] K)) := inferInstance

example (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D] [Subsingleton D] :
    (1 : WithConv ((K ⊗[k] D) →ₗ[K] K)) = 0 := Subsingleton.elim _ _

/-- Mathlib's actual product coalgebra on the empty product `Fin 0 → k`. -/
example : (inferInstance : Coalgebra k (Fin 0 → k)) = Pi.instCoalgebra := rfl

example : FiniteDimensional k (Fin 0 → k) := inferInstance

example : Subsingleton (Fin 0 → k) := inferInstance

example : K ⊗[k] WithConv ((Fin 0 → k) →ₗ[k] k) ≃ₐ[K]
    WithConv ((K ⊗[k] (Fin 0 → k)) →ₗ[K] K) :=
  convolutionDualBaseChangeEquiv k (Fin 0 → k) K

/-- The inverse formula for the empty standard basis is the empty sum. -/
example (F : WithConv ((K ⊗[k] (Fin 0 → k)) →ₗ[K] K)) :
    (convolutionDualBaseChangeEquiv k (Fin 0 → k) K).symm F = 0 := by
  rw [convolutionDualBaseChangeEquiv_symm_apply_eq_sum k (Fin 0 → k) K (Pi.basisFun k (Fin 0))]
  simp

/-- An explicit zero coalgebra on `PUnit` in the universe of `D`. -/
private abbrev punitZeroCoalgebra : Coalgebra k PUnit.{v + 1} where
  comul := 0
  counit := 0
  coassoc := Subsingleton.elim _ _
  rTensor_counit_comp_comul := Subsingleton.elim _ _
  lTensor_counit_comp_comul := Subsingleton.elim _ _

example : FiniteDimensional k PUnit.{v + 1} := inferInstance

example :
    letI := punitZeroCoalgebra.{u, v} k
    K ⊗[k] WithConv (PUnit.{v + 1} →ₗ[k] k) ≃ₐ[K]
      WithConv ((K ⊗[k] PUnit.{v + 1}) →ₗ[K] K) :=
  letI := punitZeroCoalgebra.{u, v} k
  convolutionDualBaseChangeEquiv k PUnit.{v + 1} K

end Zero

/-! ### A nonzero coalgebra -/

section Base

variable (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]

example : (inferInstance : Coalgebra k k) = CommSemiring.toCoalgebra k := rfl

/-- The convolution unit of `k` is the identity functional, and its image
evaluates to `1` at `1 ⊗ 1`. -/
example :
    convolutionDualBaseChangeEquiv k k K (1 ⊗ₜ[k] 1) (1 ⊗ₜ[k] 1) = 1 := by
  rw [convolutionDualBaseChangeEquiv_tmul_apply, LinearMap.convOne_apply]
  simp

example : (1 : K ⊗[k] WithConv (k →ₗ[k] k)) ≠ 0 := by
  intro h
  have := congrArg
    (fun x => convolutionDualBaseChangeEquiv k k K x (1 ⊗ₜ[k] 1)) h
  simp only [Algebra.TensorProduct.one_def, convolutionDualBaseChangeEquiv_tmul_apply,
    LinearMap.convOne_apply, map_zero] at this
  simp at this

/-- The inverse in the singleton basis of `k`. -/
example (F : WithConv ((K ⊗[k] k) →ₗ[K] K)) :
    (convolutionDualBaseChangeEquiv k k K).symm F =
      F (1 ⊗ₜ[k] 1) ⊗ₜ[k] toConv ((Module.Basis.singleton (Fin 1) k).coord 0) := by
  rw [convolutionDualBaseChangeEquiv_symm_apply_eq_sum k k K
    (Module.Basis.singleton (Fin 1) k)]
  simp

end Base

end Langlands.CoalgebraDescent.ConvolutionBaseChangeChecks
