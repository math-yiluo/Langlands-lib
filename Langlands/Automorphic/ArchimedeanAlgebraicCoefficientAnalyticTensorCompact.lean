import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticCompact
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Compact differentiation on actual automorphic tensors with analytic coefficients -/

noncomputable section

universe uF

open scoped Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme
open ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

local instance analyticTensorCompactRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance analyticTensorCompactContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticTensorCompactSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticTensorCompactFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance analyticTensorCompactStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance analyticTensorCompactSpaceAddCommGroup :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The original finite coefficient coordinates identify actual tensors with
finite tuples of actual automorphic vectors. -/
def tensorAnalyticCoordinates :
    (S.Space ⊗[ℂ] AnalyticSpace e ρ) ≃ₗ[ℂ] (m → S.Space) :=
  TensorProduct.congr (LinearEquiv.refl ℂ S.Space)
    ((analyticCoordinates e ρ).trans (coordinates e ρ)) ≪≫ₗ
      TensorProduct.piScalarRight ℂ ℂ S.Space m

@[simp]
theorem tensorAnalyticCoordinates_tmul (f : S.Space) (v : AnalyticSpace e ρ) (i : m) :
    tensorAnalyticCoordinates e ρ S (f ⊗ₜ[ℂ] v) i =
      coordinates e ρ (analyticCoordinates e ρ v) i • f := by
  simp [tensorAnalyticCoordinates]

private def automorphicScalarEvaluation (x : AdelicGL F n) : S.Space →ₗ[ℂ] ℂ where
  toFun f := evaluate F n (S.toContinuous f) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual scalar function evaluation after a genuine coefficient coordinate. -/
def tensorAnalyticEvaluation (x : AdelicGL F n) (i : m) :
    (S.Space ⊗[ℂ] AnalyticSpace e ρ) →ₗ[ℂ] ℂ :=
  (automorphicScalarEvaluation S x).comp
    ((LinearMap.proj i).comp (tensorAnalyticCoordinates e ρ S).toLinearMap)

@[simp]
theorem tensorAnalyticEvaluation_tmul (x : AdelicGL F n) (i : m)
    (f : S.Space) (v : AnalyticSpace e ρ) :
    tensorAnalyticEvaluation e ρ S x i (f ⊗ₜ[ℂ] v) =
      coordinates e ρ (analyticCoordinates e ρ v) i *
        evaluate F n (S.toContinuous f) x := by
  change evaluate F n (S.toContinuous
    (tensorAnalyticCoordinates e ρ S (f ⊗ₜ[ℂ] v) i)) x = _
  rw [tensorAnalyticCoordinates_tmul, map_smul]
  rfl

/-- All actual adelic evaluations and the finite coefficient coordinates
separate the original algebraic tensor product. -/
theorem tensorAnalyticEvaluation_ext
    {s t : S.Space ⊗[ℂ] AnalyticSpace e ρ}
    (h : ∀ (x : AdelicGL F n) (i : m),
      tensorAnalyticEvaluation e ρ S x i s = tensorAnalyticEvaluation e ρ S x i t) :
    s = t := by
  apply (tensorAnalyticCoordinates e ρ S).injective
  funext i
  apply S.toContinuous_injective
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact h x i

private def coefficientScalarEvaluation (i : m) : AnalyticSpace e ρ →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp ((coordinates e ρ).toLinearMap.comp
    (analyticCoordinates e ρ).toLinearMap)

/-- The product rule for the two original compact actions gives the actual
diagonal tensor Lie derivative after every scalar evaluation. -/
theorem tensorAnalyticCompactCurve_evaluate_deriv
    (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0)
    (v : S.Space ⊗[ℂ] AnalyticSpace e ρ)
    (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) (i : m) :
    HasDerivAt
      (fun t => tensorAnalyticEvaluation e ρ S (AdelicGL.pair F n a b) i
        (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) (c t) v))
      (tensorAnalyticEvaluation e ρ S (AdelicGL.pair F n a b) i
        (S.tensorComplexLieAction (AnalyticSpace e ρ) (complexify F n X) v)) 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul f v =>
    have hf := S.compactCurve_evaluate_deriv X c hc0 hc f a b
    let ℓ := coefficientScalarEvaluation e ρ i
    have hv := ((ℓ.toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (analyticCompactCurve_deriv e ρ X c hc0 hc v)
    change HasDerivAt
      (fun t => coordinates e ρ (analyticCoordinates e ρ
        (analyticCompactRepresentation e ρ (c t) v)) i)
      (coordinates e ρ (analyticCoordinates e ρ ⁅complexify F n X, v⁆) i) 0 at hv
    have hcf : S.compactRepresentation (c 0) f = f := by
      rw [hc0]
      exact congrArg (fun A : Module.End ℂ S.Space => A f) S.compactRepresentation.map_one
    have hcv : analyticCompactRepresentation e ρ (c 0) v = v := by
      rw [hc0]
      exact congrArg (fun A : Module.End ℂ (AnalyticSpace e ρ) => A v)
        (analyticCompactRepresentation e ρ).map_one
    have hd := hv.mul hf
    simp only [hcf, hcv] at hd
    let E := tensorAnalyticEvaluation e ρ S (AdelicGL.pair F n a b) i
    have hD :
        E (S.tensorComplexLieAction (AnalyticSpace e ρ) (complexify F n X) (f ⊗ₜ[ℂ] v)) =
        coordinates e ρ (analyticCoordinates e ρ ⁅complexify F n X, v⁆) i *
          evaluate F n (S.toContinuous f) (AdelicGL.pair F n a b) +
        coordinates e ρ (analyticCoordinates e ρ v) i *
          evaluate F n (S.toContinuous (S.complexLieAction (complexify F n X) f))
            (AdelicGL.pair F n a b) := by
      calc
        _ = E (S.complexLieAction (complexify F n X) f ⊗ₜ[ℂ] v) +
            E (f ⊗ₜ[ℂ] ⁅complexify F n X, v⁆) :=
          (congrArg E (S.tensorComplexLieAction_tmul (AnalyticSpace e ρ)
            (complexify F n X) f v)).trans (E.map_add _ _)
        _ = _ := by
          rw [tensorAnalyticEvaluation_tmul, tensorAnalyticEvaluation_tmul]
          exact add_comm _ _
    refine (hd.congr_deriv hD.symm).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    intro t
    exact (congrArg E (S.tensorCompactRepresentation_tmul
      (analyticCompactRepresentation e ρ) (c t) f v)).trans
        (tensorAnalyticEvaluation_tmul e ρ S (AdelicGL.pair F n a b) i
          (S.compactRepresentation (c t) f) (analyticCompactRepresentation e ρ (c t) v))
  | add v w hv hw =>
    let E := tensorAnalyticEvaluation e ρ S (AdelicGL.pair F n a b) i
    let D := S.tensorComplexLieAction (AnalyticSpace e ρ) (complexify F n X)
    have hD : E (D (v + w)) = E (D v) + E (D w) :=
      (congrArg E (D.map_add v w)).trans (E.map_add _ _)
    refine ((hv.add hw).congr_deriv hD.symm).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    intro t
    let T := S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) (c t)
    exact (congrArg E (T.map_add v w)).trans (E.map_add _ _)

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 3000000

/-- Differentiating original full compact equivariance gives tensor insertion
on complexifications of real input tuples. -/
theorem tensorAnalyticCochain_compact_real (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] (S.Space ⊗[ℂ] AnalyticSpace e ρ))
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n)
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q)
    (Y : compactLieSubalgebra F n) (X : Fin q → RealLieAlgebra F n) :
    S.tensorComplexLieAction (AnalyticSpace e ρ) (complexify F n Y.val)
        (f (fun j => complexify F n (X j))) =
      ∑ j, f (Function.update (fun k => complexify F n (X k)) j
        (complexify F n ⁅Y.val, X j⁆)) := by
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n Y
  apply tensorAnalyticEvaluation_ext e ρ S
  intro x i
  let E := tensorAnalyticEvaluation e ρ S
    (AdelicGL.pair F n (AdelicGL.infinite F n x) (AdelicGL.finite F n x)) i
  have hd := tensorAnalyticCompactCurve_evaluate_deriv e ρ S Y.val c hc0 hc
    (f (fun j => complexify F n (X j)))
    (AdelicGL.infinite F n x) (AdelicGL.finite F n x) i
  have he := compactCurve_scalarCochain_deriv F n q f E Y X c hc0 hc
  have hcurve :
      (fun t => E (f (fun j => complexify F n
        (realLieConjugation F n (c t).val (X j))))) =
      (fun t => E (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) (c t)
        (f (fun j => complexify F n (X j))))) := by
    funext t
    have hh := hf (c t) (fun j => complexify F n (X j))
    simpa only [complexCompactRepresentation_apply,
      complexLieConjugation_complexify] using congrArg E hh
  rw [hcurve] at he
  have hu := (hd.unique he).trans
    (map_sum E (fun j : Fin q => f (Function.update
      (fun k => complexify F n (X k)) j (complexify F n ⁅Y.val, X j⁆))) Finset.univ).symm
  simpa only [E, AdelicGL.pair_projections] using hu

set_option maxHeartbeats 800000

/-- The real compact insertion identity on arbitrary complex input tuples. -/
theorem tensorAnalyticCochain_compact_real_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] (S.Space ⊗[ℂ] AnalyticSpace e ρ))
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n)
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q)
    (Y : compactLieSubalgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    S.tensorComplexLieAction (AnalyticSpace e ρ) (complexify F n Y.val) (f X) =
      ∑ j, f (Function.update X j ⁅complexify F n Y.val, X j⁆) :=
  complexCochainInsertion_of_real F n q f
    (S.tensorComplexLieAction (AnalyticSpace e ρ) (complexify F n Y.val)) Y.val
    (tensorAnalyticCochain_compact_real e ρ S q f hf Y) X

/-- The actual diagonal tensor Lie action satisfies compact insertion in every
complexified compact direction, derived from the original full group action. -/
theorem tensorAnalyticCochain_compact_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] (S.Space ⊗[ℂ] AnalyticSpace e ρ))
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n)
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    S.tensorCompactLieAction (AnalyticSpace e ρ) Y (f X) =
      ∑ j, f (Function.update X j ⁅compactComplexInclusion F n Y, X j⁆) := by
  induction Y using TensorProduct.inductionOn with
  | tmul z Y =>
    change S.tensorComplexLieAction (AnalyticSpace e ρ)
      (compactComplexInclusion F n (z ⊗ₜ[ℝ] Y)) (f X) = _
    have ht : compactComplexInclusion F n (z ⊗ₜ[ℝ] Y) =
        z • complexify F n Y.val := by
      rw [compactComplexInclusion_tmul]
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht]
    let A := S.tensorComplexLieAction (AnalyticSpace e ρ)
    have ha : A (z • complexify F n Y.val) (f X) =
        z • A (complexify F n Y.val) (f X) :=
      congrArg (fun T : Module.End ℂ (S.Space ⊗[ℂ] AnalyticSpace e ρ) => T (f X))
        (A.toLinearMap.map_smul z (complexify F n Y.val))
    refine ha.trans ((congrArg (fun v : S.Space ⊗[ℂ] AnalyticSpace e ρ => z • v)
      (tensorAnalyticCochain_compact_real_complex e ρ S q f hf Y X)).trans ?_)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [_root_.smul_lie z (complexify F n Y.val) (X j)]
    exact (f.map_update_smul X j z ⁅complexify F n Y.val, X j⁆).symm
  | add Y Z hY hZ =>
    simp only [map_add, LinearMap.add_apply, add_lie, f.map_update_add,
      Finset.sum_add_distrib, hY, hZ]

/-- Actual tensor cochains obeying the compact infinitesimal insertion law. -/
def tensorAnalyticInfinitesimalCompactCochains (q : ℕ) :
    Submodule ℂ ((ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] AnalyticSpace e ρ)) where
  carrier := {f | ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n),
    S.tensorCompactLieAction (AnalyticSpace e ρ) Y (f X) =
      ∑ j, f (Function.update X j ⁅compactComplexInclusion F n Y, X j⁆)}
  zero_mem' := by intro Y X; simp
  add_mem' hf hg := by
    intro Y X
    simpa only [AlternatingMap.add_apply, map_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hf Y X) (hg Y X)
  smul_mem' z f hf := by
    intro Y X
    simpa only [AlternatingMap.smul_apply, map_smul, Finset.smul_sum] using
      congrArg (fun v : S.Space ⊗[ℂ] AnalyticSpace e ρ => z • v) (hf Y X)

/-- Identity on actual tensor cochains, with infinitesimal membership proved by
differentiating the original compact action. -/
def tensorAnalyticCompactEquivariantLieInclusion (q : ℕ) :
    HorizontalAlternating.equivariant
      (complexCompactRepresentation F n)
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q →ₗ[ℂ]
        tensorAnalyticInfinitesimalCompactCochains e ρ S q where
  toFun f := ⟨f.val, tensorAnalyticCochain_compact_complex e ρ S q f.val f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem tensorAnalyticCompactEquivariantLieInclusion_coe (q : ℕ)
    (f : HorizontalAlternating.equivariant
      (complexCompactRepresentation F n)
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q) :
    (tensorAnalyticCompactEquivariantLieInclusion e ρ S q f).val = f.val := rfl

theorem tensorAnalyticCompactEquivariantLieInclusion_injective (q : ℕ) :
    Function.Injective (tensorAnalyticCompactEquivariantLieInclusion e ρ S q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : tensorAnalyticInfinitesimalCompactCochains e ρ S q => v.val) h)

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
