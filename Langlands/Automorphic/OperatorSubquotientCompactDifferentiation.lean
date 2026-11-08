import Langlands.Automorphic.OperatorSubquotientLieAction
import Langlands.Automorphic.ReducedCochainCompactDifferentiation

/-!
# Compact differentiation on actual automorphic operator quotients

Compact translation of an actual realized vector is differentiated against an
arbitrary complex linear functional, using compact finiteness and point
evaluations. The result descends to every actual operator subquotient and gives
its infinitesimal compact invariants and compact cochain insertion identities.
-/

noncomputable section

universe uF

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions
open ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientCompactDiffRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientCompactDiffContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientCompactDiffSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientCompactDiffFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientCompactDiffStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientCompactDiffRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Compact differentiation against linear functionals -/

section DualDerivative

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A complex Lie action differentiates a compact representation against every complex
linear functional along every compact curve through the identity with a given real
tangent direction. -/
def CompactDualDerivative (ρ : Representation ℂ (standardInfiniteCompact F n) V)
    (A : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  ∀ (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n), c 0 = 1 →
    HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0 →
    ∀ (μ : V →ₗ[ℂ] ℂ) (v : V),
      HasDerivAt (fun t : ℝ => μ (ρ (c t) v)) (μ (A (complexify F n X) v)) 0

namespace CompactDualDerivative

variable {ρ : Representation ℂ (standardInfiniteCompact F n) V}
  {A : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- Real compact directions kill vectors fixed by the full compact group. -/
theorem real_eq_zero_of_fixed (hA : CompactDualDerivative ρ A) (v : V)
    (hv : v ∈ ρ.invariants) (X : compactLieSubalgebra F n) :
    A (complexify F n X.val) v = 0 := by
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n X
  have hfix : ∀ k, ρ k v = v := (Representation.mem_invariants ρ v).mp hv
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp ?_
  intro μ
  have hconst : HasDerivAt (fun t : ℝ => μ (ρ (c t) v)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (μ v)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => congrArg μ (hfix (c t))))
  exact (hA X.val c hc0 hc μ v).unique hconst

/-- Complexified compact directions kill vectors fixed by the full compact group. -/
theorem compact_eq_zero_of_fixed (hA : CompactDualDerivative ρ A) (v : V)
    (hv : v ∈ ρ.invariants) (Y : CompactComplexLieAlgebra F n) :
    A (compactComplexInclusion F n Y) v = 0 := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    rw [compactComplexInclusion_tmul]
    have ht : z ⊗ₜ[ℝ] X.val = z • complexify F n X.val := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, LinearMap.smul_apply, hA.real_eq_zero_of_fixed v hv X, smul_zero]
  | add Y Z hY hZ =>
    simp only [map_add, LinearMap.add_apply, hY, hZ, add_zero]

/-- Full compact equivariance of a cochain gives the real infinitesimal insertion
identity on complexified real tuples. -/
theorem cochain_compact_real (hA : CompactDualDerivative ρ A) (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (hf : f ∈ HorizontalAlternating.equivariant (complexCompactRepresentation F n) ρ q)
    (Y : compactLieSubalgebra F n) (X : Fin q → RealLieAlgebra F n) :
    A (complexify F n Y.val) (f (fun i => complexify F n (X i))) =
      ∑ i, f (Function.update (fun j => complexify F n (X j)) i
        (complexify F n ⁅Y.val, X i⁆)) := by
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n Y
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro μ
  have hd := hA Y.val c hc0 hc μ (f (fun i => complexify F n (X i)))
  have he := compactCurve_scalarCochain_deriv F n q f μ Y X c hc0 hc
  have hcurve :
      (fun t => μ (f (fun i => complexify F n (realLieConjugation F n (c t).val (X i))))) =
      (fun t => μ (ρ (c t) (f (fun i => complexify F n (X i))))) := by
    funext t
    have hh := hf (c t) (fun i => complexify F n (X i))
    simpa only [complexCompactRepresentation_apply,
      complexLieConjugation_complexify] using congrArg μ hh
  rw [hcurve] at he
  rw [map_sub, hd.unique he, map_sum, sub_self]

/-- The real compact insertion identity on arbitrary complex cochain inputs. -/
theorem cochain_compact_real_complex (hA : CompactDualDerivative ρ A) (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (hf : f ∈ HorizontalAlternating.equivariant (complexCompactRepresentation F n) ρ q)
    (Y : compactLieSubalgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    A (complexify F n Y.val) (f X) =
      ∑ i, f (Function.update X i ⁅complexify F n Y.val, X i⁆) :=
  complexCochainInsertion_of_real F n q f (A (complexify F n Y.val)) Y.val
    (hA.cochain_compact_real q f hf Y) X

/-- Full compact equivariance gives the complex compact infinitesimal insertion
identity in every degree. -/
theorem cochain_compact_complex (hA : CompactDualDerivative ρ A) (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] V)
    (hf : f ∈ HorizontalAlternating.equivariant (complexCompactRepresentation F n) ρ q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    A (compactComplexInclusion F n Y) (f X) =
      ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆) := by
  induction Y using TensorProduct.inductionOn with
  | tmul z Y =>
    rw [compactComplexInclusion_tmul]
    have ht : z ⊗ₜ[ℝ] Y.val = z • complexify F n Y.val := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, LinearMap.smul_apply, hA.cochain_compact_real_complex q f hf Y X,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.smul_lie z (complexify F n Y.val) (X i)]
    exact (f.map_update_smul X i z ⁅complexify F n Y.val, X i⁆).symm
  | add Y Z hY hZ =>
    simp only [map_add, LinearMap.add_apply, add_lie, f.map_update_add,
      Finset.sum_add_distrib, hY, hZ]

end CompactDualDerivative

end DualDerivative

namespace OperatorRealization

variable (S : OperatorRealization F n)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of an actual realized vector at an adelic point. -/
def pointEvaluation (x : AdelicGL F n) : S.Space →ₗ[ℂ] ℂ where
  toFun v := evaluate F n (S.toContinuous v) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pointEvaluation_apply (x : AdelicGL F n) (v : S.Space) :
    S.pointEvaluation x v = evaluate F n (S.toContinuous v) x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Point evaluations separate actual realized vectors. -/
theorem eq_zero_of_pointEvaluation (v : S.Space)
    (hv : ∀ x : AdelicGL F n, S.pointEvaluation x v = 0) : v = 0 := by
  apply S.toContinuous_injective
  rw [map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hv x

set_option backward.isDefEq.respectTransparency false in
/-- On a finite-dimensional subspace, point evaluations span the whole dual. -/
theorem span_pointEvaluation_eq_top (W : Submodule ℂ S.Space) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun x : AdelicGL F n => (S.pointEvaluation x).comp W.subtype) =
      ⊤ := by
  have : FiniteDimensional ℂ (Module.Dual ℂ W) := Subspace.instModuleDualFiniteDimensional
  let E : Submodule ℂ (Module.Dual ℂ W) :=
    Submodule.span ℂ (Set.range fun x : AdelicGL F n => (S.pointEvaluation x).comp W.subtype)
  have : FiniteDimensional ℂ E := FiniteDimensional.finiteDimensional_submodule E
  have hco : E.dualCoannihilator = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    apply Subtype.ext
    exact S.eq_zero_of_pointEvaluation w.val
      (fun x => hw _ (Submodule.subset_span ⟨x, rfl⟩))
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [hco, Submodule.dualAnnihilator_bot] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- On a finite-dimensional subspace, derivatives of all point evaluations of a curve
give the derivative of every complex linear functional of that curve. -/
theorem hasDerivAt_dual_of_pointEvaluation (W : Submodule ℂ S.Space) [FiniteDimensional ℂ W]
    (g : ℝ → W) (w : W)
    (hg : ∀ x : AdelicGL F n,
      HasDerivAt (fun t : ℝ => S.pointEvaluation x (g t)) (S.pointEvaluation x w) 0)
    (μ : S.Space →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t : ℝ => μ (g t)) (μ w) 0 := by
  have key : ∀ φ ∈ Submodule.span ℂ (Set.range fun x : AdelicGL F n =>
      (S.pointEvaluation x).comp W.subtype),
      HasDerivAt (fun t : ℝ => φ (g t)) (φ w) 0 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨x, rfl⟩ := hφ
      exact hg x
    | zero =>
      exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
    | add φ ψ _ _ hφ hψ =>
      exact hφ.add hψ
    | smul a φ _ hφ =>
      exact hφ.const_mul a
  exact key (μ.comp W.subtype) ((S.span_pointEvaluation_eq_top W).symm ▸ Submodule.mem_top)

set_option backward.isDefEq.respectTransparency false in
/-- Compact translation is differentiated against every linear functional,
using the finite-dimensional compact orbit span and point evaluations. -/
theorem compactCurve_dual_deriv
    (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0)
    (μ : S.Space →ₗ[ℂ] ℂ) (f : S.Space) :
    HasDerivAt (fun t : ℝ => μ (S.compactRepresentation (c t) f))
      (μ (S.complexLieAction (complexify F n X) f)) 0 := by
  have hfin : Module.Finite ℂ (FiniteVectors.orbitSpan S.compactRepresentation f) :=
    S.compactRepresentation_isFiniteVector f
  have hW : FiniteDimensional ℂ ↥(FiniteVectors.orbitSpan S.compactRepresentation f ⊔
      Submodule.span ℂ {S.complexLieAction (complexify F n X) f}) :=
    Submodule.finiteDimensional_sup _ _
  exact S.hasDerivAt_dual_of_pointEvaluation
    (FiniteVectors.orbitSpan S.compactRepresentation f ⊔
      Submodule.span ℂ {S.complexLieAction (complexify F n X) f})
    (fun t => ⟨_, Submodule.mem_sup_left (FiniteVectors.action_mem_orbitSpan _ (c t) f)⟩)
    ⟨_, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩
    (fun x => by
      have h := S.compactCurve_evaluate_deriv X c hc0 hc f
        (AdelicGL.infinite F n x) (AdelicGL.finite F n x)
      rw [AdelicGL.pair_projections] at h
      exact h) μ

/-- Actual realized vectors satisfy compact differentiation against linear functionals. -/
theorem compactDualDerivative :
    CompactDualDerivative S.compactRepresentation S.complexLieAction :=
  fun X c hc0 hc μ f => S.compactCurve_dual_deriv X c hc0 hc μ f

end OperatorRealization

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- On a projected representative, quotient compact translation is differentiated
against every linear functional through the numerator statement. -/
theorem compactCurve_dual_deriv_projection
    (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0)
    (μ : Q.Space →ₗ[ℂ] ℂ) (v : Q.upper.Space) :
    HasDerivAt (fun t : ℝ => μ (Q.compactRepresentation (c t) (Q.projection v)))
      (μ (Q.complexLieAction (complexify F n X) (Q.projection v))) 0 :=
  Q.upper.compactCurve_dual_deriv X c hc0 hc (μ.comp Q.projection.toLinearMap) v

/-- Quotient compact translation is differentiated against every linear functional. -/
theorem compactCurve_dual_deriv
    (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0)
    (μ : Q.Space →ₗ[ℂ] ℂ) (f : Q.Space) :
    HasDerivAt (fun t : ℝ => μ (Q.compactRepresentation (c t) f))
      (μ (Q.complexLieAction (complexify F n X) f)) 0 := by
  induction f using Submodule.Quotient.induction_on with
  | H v => exact Q.compactCurve_dual_deriv_projection X c hc0 hc μ v

/-- Quotient vectors satisfy compact differentiation against linear functionals. -/
theorem compactDualDerivative :
    CompactDualDerivative Q.compactRepresentation Q.complexLieAction :=
  fun X c hc0 hc μ f => Q.compactCurve_dual_deriv X c hc0 hc μ f

/-- Real compact directions kill quotient vectors fixed by the full compact group. -/
theorem complexLieAction_compact_real_eq_zero (f : Q.Space)
    (hf : f ∈ Q.compactRepresentation.invariants)
    (X : compactLieSubalgebra F n) :
    Q.complexLieAction (complexify F n X.val) f = 0 :=
  Q.compactDualDerivative.real_eq_zero_of_fixed f hf X

/-- Full compact invariance implies invariance for the quotient complex compact Lie action. -/
theorem compactLieAction_eq_zero_of_fixed (f : Q.Space)
    (hf : f ∈ Q.compactRepresentation.invariants)
    (Y : CompactComplexLieAlgebra F n) :
    Q.compactLieAction Y f = 0 :=
  (Q.compactLieAction_apply Y f).trans
    (Q.compactDualDerivative.compact_eq_zero_of_fixed f hf Y)

/-- The identity on quotient vectors, with infinitesimal membership proved by differentiation. -/
def compactFixedLieInclusion :
    Q.compactRepresentation.invariants →ₗ[ℂ]
      LieModule.maxTrivSubmodule ℂ (CompactComplexLieAlgebra F n) Q.Space where
  toFun f := ⟨f.val, fun Y => by
    rw [Q.compact_lie_eq]
    exact Q.compactLieAction_eq_zero_of_fixed f.val f.property Y⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem compactFixedLieInclusion_coe (f : Q.compactRepresentation.invariants) :
    (Q.compactFixedLieInclusion f : Q.Space) = f.val := rfl

theorem compactFixedLieInclusion_injective : Function.Injective Q.compactFixedLieInclusion := by
  intro f g h
  have hv : f.val = g.val :=
    congrArg (fun v : LieModule.maxTrivSubmodule ℂ
      (CompactComplexLieAlgebra F n) Q.Space => v.val) h
  exact Subtype.ext hv

/-! ## Compact cochain insertion identities -/

/-- Actual full compact equivariance of a quotient-valued cochain implies the real
infinitesimal insertion identity on complexified real tuples. -/
theorem cochain_compact_real (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) Q.compactRepresentation q)
    (Y : compactLieSubalgebra F n) (X : Fin q → RealLieAlgebra F n) :
    Q.complexLieAction (complexify F n Y.val) (f (fun i => complexify F n (X i))) =
      ∑ i, f (Function.update (fun j => complexify F n (X j)) i
        (complexify F n ⁅Y.val, X i⁆)) :=
  Q.compactDualDerivative.cochain_compact_real q f hf Y X

/-- The real compact insertion identity on arbitrary complex quotient cochain inputs. -/
theorem cochain_compact_real_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) Q.compactRepresentation q)
    (Y : compactLieSubalgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    Q.complexLieAction (complexify F n Y.val) (f X) =
      ∑ i, f (Function.update X i ⁅complexify F n Y.val, X i⁆) :=
  Q.compactDualDerivative.cochain_compact_real_complex q f hf Y X

/-- Full compact equivariance implies the complex compact infinitesimal insertion
identity for quotient-valued cochains in every degree. -/
theorem cochain_compact_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) Q.compactRepresentation q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    Q.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆) :=
  (Q.compactLieAction_apply Y (f X)).trans
    (Q.compactDualDerivative.cochain_compact_complex q f hf Y X)

/-- Quotient-valued cochains satisfying the complex compact infinitesimal insertion identity. -/
def infinitesimalCompactCochains (q : ℕ) :
    Submodule ℂ ((ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space) where
  carrier := {f | ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n),
    Q.compactLieAction Y (f X) =
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
      congrArg (fun v : Q.Space => z • v) (hf Y X)

@[simp]
theorem mem_infinitesimalCompactCochains (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space) :
    f ∈ Q.infinitesimalCompactCochains q ↔
      ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n),
        Q.compactLieAction Y (f X) =
          ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆) := Iff.rfl

/-- Identity inclusion with infinitesimal membership derived from quotient full
compact equivariance. -/
def compactEquivariantLieInclusion (q : ℕ) :
    HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) Q.compactRepresentation q →ₗ[ℂ]
        Q.infinitesimalCompactCochains q where
  toFun f := ⟨f.val, Q.cochain_compact_complex q f.val f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem compactEquivariantLieInclusion_coe (q : ℕ)
    (f : HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) Q.compactRepresentation q) :
    (Q.compactEquivariantLieInclusion q f).val = f.val := rfl

theorem compactEquivariantLieInclusion_injective (q : ℕ) :
    Function.Injective (Q.compactEquivariantLieInclusion q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : Q.infinitesimalCompactCochains q => v.val) h)

/-! ## Reduced horizontal cochains -/

section Reduced

variable [NeZero n]

/-- Differentiate quotient full compact equivariance on the reduced complex algebra. -/
theorem reducedCochain_compact_complex (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (reducedCompactRepresentation F n) Q.compactRepresentation q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ReducedComplexLieAlgebra F n) :
    Q.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆) := by
  have he := Q.cochain_compact_complex q (reducedCochainExtension F n q f)
    (reducedCochainExtension_equivariant F n Q.compactRepresentation q f hf)
    Y (fun i => reducedComplexInclusion F n (X i))
  have hvalue := congrArg (Q.compactLieAction Y)
    (reducedCochainExtension_inclusion F n q f X).symm
  refine hvalue.trans (he.trans ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [reducedCochainExtension_apply]
  apply congrArg f
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, (reducedComplexProjection F n).map_lie,
      reducedComplexProjection_compact, reducedComplexProjection_inclusion]
  · simp only [Function.update_of_ne hj, reducedComplexProjection_inclusion]

/-- Reduced quotient-valued cochains satisfying the complex compact insertion identity. -/
def reducedInfinitesimalCompactCochains (q : ℕ) :
    Submodule ℂ ((ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space) where
  carrier := {f | ∀ (Y : CompactComplexLieAlgebra F n)
      (X : Fin q → ReducedComplexLieAlgebra F n),
    Q.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆)}
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
      congrArg (fun v : Q.Space => z • v) (hf Y X)

omit [NeZero n] in
@[simp]
theorem mem_reducedInfinitesimalCompactCochains (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space) :
    f ∈ Q.reducedInfinitesimalCompactCochains q ↔
      ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ReducedComplexLieAlgebra F n),
        Q.compactLieAction Y (f X) =
          ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆) := Iff.rfl

/-- The identity inclusion whose infinitesimal membership is derived by differentiation. -/
def reducedCompactEquivariantLieInclusion (q : ℕ) :
    HorizontalAlternating.equivariant
      (reducedCompactRepresentation F n) Q.compactRepresentation q →ₗ[ℂ]
        Q.reducedInfinitesimalCompactCochains q where
  toFun f := ⟨f.val, Q.reducedCochain_compact_complex q f.val f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem reducedCompactEquivariantLieInclusion_coe (q : ℕ)
    (f : HorizontalAlternating.equivariant
      (reducedCompactRepresentation F n) Q.compactRepresentation q) :
    (Q.reducedCompactEquivariantLieInclusion q f).val = f.val := rfl

theorem reducedCompactEquivariantLieInclusion_injective (q : ℕ) :
    Function.Injective (Q.reducedCompactEquivariantLieInclusion q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : Q.reducedInfinitesimalCompactCochains q => v.val) h)

/-- Horizontal reduced quotient cochains satisfying the infinitesimal compact identity. -/
def infinitesimalHorizontalCochains (q : ℕ) :
    Submodule ℂ ((ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space) :=
  HorizontalAlternating.horizontal (compactInReducedSubmodule F n) q ⊓
    Q.reducedInfinitesimalCompactCochains q

/-- Retain horizontality while deriving infinitesimal membership from the full compact group. -/
def horizontalCompactLieInclusion (q : ℕ) :
    horizontalEquivariantSubmodule F n Q.compactRepresentation q →ₗ[ℂ]
      Q.infinitesimalHorizontalCochains q where
  toFun f := ⟨f.val, f.property.1, Q.reducedCochain_compact_complex q f.val f.property.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem horizontalCompactLieInclusion_coe (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q) :
    (Q.horizontalCompactLieInclusion q f).val = f.val := rfl

theorem horizontalCompactLieInclusion_injective (q : ℕ) :
    Function.Injective (Q.horizontalCompactLieInclusion q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : Q.infinitesimalHorizontalCochains q => v.val) h)

end Reduced

end OperatorSubquotient
end Langlands.Automorphic
