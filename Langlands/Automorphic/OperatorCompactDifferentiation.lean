import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RepresentationTheory.Invariants

/-! # Compact fixed vectors and actual infinitesimal invariants -/

noncomputable section
universe u

open scoped TensorProduct Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Pointwise differentiation of actual compact translation gives the actual Lie action. -/
theorem compactCurve_evaluate_deriv
    (X : ArchimedeanGL.RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (ArchimedeanGL.realLieAlgebraToMatrix F n X) 0)
    (f : S.Space) (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    HasDerivAt
      (fun t : ℝ => evaluate F n (S.toContinuous (S.compactRepresentation (c t) f))
        (AdelicGL.pair F n a b))
      (evaluate F n (S.toContinuous
        (S.complexLieAction (ArchimedeanGL.complexify F n X) f))
          (AdelicGL.pair F n a b)) 0 := by
  convert ArchimedeanGL.compactCurve_right_deriv F n X c hc0 hc
    (finiteSmoothSlice F n b f.val.val) a using 1
  · funext t
    rw [S.evaluate_compactRepresentation]
    change evaluate F n f.val.val.val
      (AdelicGL.pair F n a b * AdelicGL.ofInfinite F n (c t).val) =
        evaluate F n f.val.val.val (AdelicGL.pair F n (a * (c t).val) b)
    rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]
  · change evaluate F n
      (finiteSmoothEnvelopingAction F n
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X))
          f.val.val).val (AdelicGL.pair F n a b) = _
    rw [evaluate_finiteSmoothEnvelopingAction, ArchimedeanGL.envelopingAction_real_generator]

/-- Every scalar evaluation of the real compact derivative of a fixed vector vanishes. -/
theorem evaluate_complexLieAction_compact_real_eq_zero (f : S.Space)
    (hf : f ∈ S.compactRepresentation.invariants)
    (X : ArchimedeanGL.compactLieSubalgebra F n)
    (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    evaluate F n
      (S.toContinuous (S.complexLieAction (ArchimedeanGL.complexify F n X.val) f))
        (AdelicGL.pair F n a b) = 0 := by
  change ∀ k, S.compactRepresentation k f = f at hf
  obtain ⟨c, hc0, hc⟩ := ArchimedeanGL.compactTangentCurve F n X
  have hd := S.compactCurve_evaluate_deriv X.val c hc0 hc f a b
  have hconst : HasDerivAt
      (fun t : ℝ => evaluate F n (S.toContinuous (S.compactRepresentation (c t) f))
        (AdelicGL.pair F n a b)) 0 0 :=
    (hasDerivAt_const (0 : ℝ)
      (evaluate F n (S.toContinuous f) (AdelicGL.pair F n a b))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun t => congrArg
          (fun v : S.Space => evaluate F n (S.toContinuous v) (AdelicGL.pair F n a b))
            (hf (c t))))
  exact hd.unique hconst

/-- A vector fixed by the full compact group is killed by every real compact direction. -/
theorem complexLieAction_compact_real_eq_zero (f : S.Space)
    (hf : f ∈ S.compactRepresentation.invariants)
    (X : ArchimedeanGL.compactLieSubalgebra F n) :
    S.complexLieAction (ArchimedeanGL.complexify F n X.val) f = 0 := by
  apply S.toContinuous_injective
  rw [map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate F n
    (S.toContinuous (S.complexLieAction (ArchimedeanGL.complexify F n X.val) f)) x = 0
  have h := S.evaluate_complexLieAction_compact_real_eq_zero f hf X
    (AdelicGL.infinite F n x) (AdelicGL.finite F n x)
  simpa only [AdelicGL.pair_projections] using h

/-- Full compact invariance implies invariance for the actual complex compact Lie action. -/
theorem compactLieAction_eq_zero_of_fixed (f : S.Space)
    (hf : f ∈ S.compactRepresentation.invariants)
    (Y : ArchimedeanGL.CompactComplexLieAlgebra F n) :
    S.compactLieAction Y f = 0 := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    rw [compactLieAction_apply, ArchimedeanGL.compactComplexInclusion_tmul]
    have ht : z ⊗ₜ[ℝ] X.val =
        z • ArchimedeanGL.complexify F n X.val := by
      simp only [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    calc
      _ = S.complexLieAction (z • ArchimedeanGL.complexify F n X.val) f :=
        congrArg (fun U : ArchimedeanGL.ComplexLieAlgebra F n => S.complexLieAction U f) ht
      _ = z • (S.complexLieAction (ArchimedeanGL.complexify F n X.val) f) :=
        congrArg (fun A : Module.End ℂ S.Space => A f)
          (S.complexLieAction.toLinearMap.map_smul z (ArchimedeanGL.complexify F n X.val))
      _ = 0 := (congrArg (fun v : S.Space => z • v)
        (S.complexLieAction_compact_real_eq_zero f hf X)).trans (smul_zero z)
  | add Y Z hY hZ =>
    rw [map_add, LinearMap.add_apply, hY, hZ, add_zero]

/-- The identity on vectors, with infinitesimal membership proved by differentiation. -/
def compactFixedLieInclusion :
    S.compactRepresentation.invariants →ₗ[ℂ]
      LieModule.maxTrivSubmodule ℂ (ArchimedeanGL.CompactComplexLieAlgebra F n) S.Space where
  toFun f := ⟨f.val, fun Y => by
    rw [S.compact_lie_eq]
    exact S.compactLieAction_eq_zero_of_fixed f.val f.property Y⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem compactFixedLieInclusion_coe (f : S.compactRepresentation.invariants) :
    (S.compactFixedLieInclusion f : S.Space) = f.val := rfl

theorem compactFixedLieInclusion_injective : Function.Injective S.compactFixedLieInclusion := by
  intro f g h
  have hv : f.val = g.val :=
    congrArg (fun v : LieModule.maxTrivSubmodule ℂ
      (ArchimedeanGL.CompactComplexLieAlgebra F n) S.Space => v.val) h
  exact Subtype.ext hv

@[simp]
theorem evaluate_compactFixedLieInclusion (f : S.compactRepresentation.invariants)
    (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (S.compactFixedLieInclusion f)) x =
      evaluate F n (S.toContinuous f.val) x := rfl

end OperatorRealization
end Langlands.Automorphic
