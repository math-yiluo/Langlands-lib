import Langlands.Coefficients.DiscreteAdicCompletion
import Langlands.Shimura.Coefficients.CongruenceDiagram
import Langlands.Shimura.Coefficients.CongruenceLimitAction

/-! # Continuous congruence-limit actions on actual completed coefficient modules -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite Langlands.Coefficients
open DiscreteAdicCompletion

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

section General

variable {R : Type u} [CommRing R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : CompactOpenLevel G) (I : Ideal R)
variable (M : Action (ModuleCat.{w} R) U.subgroup)
variable (hN : ∀ n : ℕ, IsOpen (congruenceKernel I M n : Set U.subgroup))

/-- The actual kernel-factored action on a discrete coefficient quotient is linear and continuous. -/
def congruenceReductionLinear (n : ℕ) (g : U.subgroup ⧸ congruenceKernel I M n) :
    Reduction I M.V n →L[R] Reduction I M.V n where
  toLinearMap := ((quotientTorsionAction I M n (congruenceKernel I M n) le_rfl).ρ g).hom
  cont := continuous_of_discreteTopology

omit [IsTopologicalGroup G] in
/-- These actual linear actions commute with the original quotient transitions. -/
theorem congruenceReductionLinear_transition {i j : ℕ} (h : i ≤ j)
    (g : U.subgroup ⧸ congruenceKernel I M j) (x : Reduction I M.V j) :
    DiscreteAdicCompletion.transition I M.V h (congruenceReductionLinear U I M j g x) =
      congruenceReductionLinear U I M i (torsionCongruenceTransition I M h g)
        (DiscreteAdicCompletion.transition I M.V h x) :=
  congrArg (fun a : (torsionAction I M j).V ⟶ (torsionAction I M i).V => a x)
    ((congruenceCoefficientDiagram I M).comm (homOfLE h).op g)

/-- Coordinatewise translation preserves the actual compatible-family completion. -/
def congruenceCompletionTranslate (g : congruenceGroupLimit U I M hN) :
    Completion I M.V →L[R] Completion I M.V where
  toLinearMap :=
    { toFun x :=
        ⟨fun n => congruenceReductionLinear U I M n (congruenceGroupLimitProjection U I M hN (op n) g) (eval I M.V n x), by
          intro i j h
          change DiscreteAdicCompletion.transition I M.V h
            (congruenceReductionLinear U I M j (congruenceGroupLimitProjection U I M hN (op j) g) (eval I M.V j x)) =
              congruenceReductionLinear U I M i (congruenceGroupLimitProjection U I M hN (op i) g) (eval I M.V i x)
          rw [congruenceReductionLinear_transition]
          have hg : torsionCongruenceTransition I M h (congruenceGroupLimitProjection U I M hN (op j) g) = congruenceGroupLimitProjection U I M hN (op i) g :=
            g.property (homOfLE h).op
          rw [hg]
          exact congrArg (congruenceReductionLinear U I M i (congruenceGroupLimitProjection U I M hN (op i) g)) (x.property h)⟩
      map_add' x y := by
        apply AdicCompletion.ext
        intro n
        exact (congruenceReductionLinear U I M n (congruenceGroupLimitProjection U I M hN (op n) g)).map_add _ _
      map_smul' r x := by
        apply AdicCompletion.ext
        intro n
        exact (congruenceReductionLinear U I M n (congruenceGroupLimitProjection U I M hN (op n) g)).map_smul r _ }
  cont := (continuous_iff I M.V _).mpr fun n =>
    (congruenceReductionLinear U I M n (congruenceGroupLimitProjection U I M hN (op n) g)).continuous.comp
      (eval I M.V n).continuous

@[simp] theorem congruenceCompletionTranslate_eval (g : congruenceGroupLimit U I M hN)
    (x : Completion I M.V) (n : ℕ) :
    eval I M.V n (congruenceCompletionTranslate U I M hN g x) =
      congruenceReductionLinear U I M n (congruenceGroupLimitProjection U I M hN (op n) g) (eval I M.V n x) :=
  rfl

/-- The profinite congruence group acts by actual continuous linear endomorphisms. -/
def congruenceCompletionRepresentation :
    congruenceGroupLimit U I M hN →* (Completion I M.V →L[R] Completion I M.V) where
  toFun := congruenceCompletionTranslate U I M hN
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    change ((quotientTorsionAction I M n (congruenceKernel I M n) le_rfl).ρ 1).hom
      (x.val n) = x.val n
    rw [map_one]
    rfl
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    change ((quotientTorsionAction I M n (congruenceKernel I M n) le_rfl).ρ
      (congruenceGroupLimitProjection U I M hN (op n) g *
        congruenceGroupLimitProjection U I M hN (op n) h)).hom (x.val n) =
        ((quotientTorsionAction I M n (congruenceKernel I M n) le_rfl).ρ
          (congruenceGroupLimitProjection U I M hN (op n) g)).hom
            (((quotientTorsionAction I M n (congruenceKernel I M n) le_rfl).ρ
              (congruenceGroupLimitProjection U I M hN (op n) h)).hom (x.val n))
    rw [map_mul]
    rfl

/-- The constructed action is jointly continuous for the actual product-induced topology. -/
theorem congruenceCompletionRepresentation_continuous :
    Continuous (fun p : congruenceGroupLimit U I M hN × Completion I M.V =>
      congruenceCompletionRepresentation U I M hN p.1 p.2) := by
  apply (continuous_iff I M.V _).mpr
  intro n
  let _ := QuotientGroup.discreteTopology (hN n)
  have ha : Continuous (fun p : (U.subgroup ⧸ congruenceKernel I M n) × Reduction I M.V n =>
      congruenceReductionLinear U I M n p.1 p.2) :=
    continuous_of_discreteTopology
  exact ha.comp
    (((congruenceGroupLimitProjection U I M hN (op n)).continuous.comp continuous_fst).prodMk
      ((eval I M.V n).continuous.comp continuous_snd))

/-- The same actual linear action as an object of the module action category. -/
def congruenceCompletionAction :
    Action (ModuleCat.{w} R) (congruenceGroupLimit U I M hN) where
  V := ModuleCat.of R (Completion I M.V)
  ρ :=
    { toFun g := ModuleCat.ofHom (congruenceCompletionRepresentation U I M hN g).toLinearMap
      map_one' := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact DFunLike.congr_fun (congruenceCompletionRepresentation U I M hN).map_one x
      map_mul' g h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact DFunLike.congr_fun ((congruenceCompletionRepresentation U I M hN).map_mul g h) x }

/-- Every actual coefficient evaluation is equivariant along the group-limit projection. -/
def congruenceCompletionEvaluation (n : ℕ) :
    congruenceCompletionAction U I M hN ⟶
      (Action.res (ModuleCat.{w} R)
        (congruenceGroupLimitProjection U I M hN (op n)).toMonoidHom).obj
          (quotientTorsionAction I M n (congruenceKernel I M n) le_rfl) where
  hom := ModuleCat.ofHom (eval I M.V n).toLinearMap
  comm g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The same maps acting on the actual topological completion. -/
def congruenceCompletionTopologicalAction :
    Action TopCat.{w} (congruenceGroupLimit U I M hN) where
  V := TopCat.of (Completion I M.V)
  ρ :=
    { toFun g := TopCat.ofHom
        { toFun := congruenceCompletionRepresentation U I M hN g
          continuous_toFun := (congruenceCompletionRepresentation U I M hN g).continuous }
      map_one' := by
        apply TopCat.ext
        intro x
        exact DFunLike.congr_fun (congruenceCompletionRepresentation U I M hN).map_one x
      map_mul' g h := by
        apply TopCat.ext
        intro x
        exact DFunLike.congr_fun ((congruenceCompletionRepresentation U I M hN).map_mul g h) x }

/-- Bundle the proved joint continuity in Mathlib's continuous action category. -/
def congruenceCompletionContinuousAction :
    ContAction TopCat.{w} (congruenceGroupLimit U I M hN) :=
  ⟨congruenceCompletionTopologicalAction U I M hN,
    (Action.isContinuous_def _).mpr (congruenceCompletionRepresentation_continuous U I M hN)⟩

/-- Restriction along the original level map recovers its actual induced completion action. -/
@[simp] theorem congruenceCompletionRepresentation_original (g : U.subgroup) :
    congruenceCompletionRepresentation U I M hN (congruenceGroupLimitMap U I M hN g) =
      DiscreteAdicCompletion.map I (M.ρ g).hom := by
  apply ContinuousLinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  rfl

/-- The original integral coefficient quotient map is equivariant in every completion coordinate. -/
@[simp] theorem congruenceCompletionRepresentation_of (g : U.subgroup) (x : M.V) :
    congruenceCompletionRepresentation U I M hN (congruenceGroupLimitMap U I M hN g)
        (DiscreteAdicCompletion.of I x) =
      DiscreteAdicCompletion.of I ((M.ρ g).hom x) := by
  rw [congruenceCompletionRepresentation_original, DiscreteAdicCompletion.map_of]

end General

section AlgebraicCompact

open Langlands.Global

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
variable (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ) (hm : m ≠ 0)

/-- The actual compatible-quotient completion of the constructed stable algebraic coefficient lattice. -/
abbrev algebraicCompactCoefficientCompletion :=
  Completion (coefficientScalarIdeal l m) (algebraicCompactCoefficientLattice ρ p l U).action.V

include hm in
/-- Finiteness of the actual torsion reductions proves compactness of this completion. -/
theorem algebraicCompactCoefficientCompletion_compact :
    CompactSpace (algebraicCompactCoefficientCompletion ρ p l U m) := by
  let (n : ℕ) : Finite
      ((algebraicCompactCoefficientLattice ρ p l U).action.V ⧸
        (coefficientScalarIdeal l m ^ n • ⊤ :
          Submodule (CoefficientIntegers l) (algebraicCompactCoefficientLattice ρ p l U).action.V)) :=
    (algebraicCompactCoefficientLattice ρ p l U).rationalTorsionSystem_finite l m hm n
  infer_instance

/-- The actual algebraic congruence-limit action by continuous linear endomorphisms. -/
def algebraicCompactCoefficientCompletionRepresentation :
    algebraicCompactCongruenceGroupLimit ρ p l U m hm →*
      (algebraicCompactCoefficientCompletion ρ p l U m →L[CoefficientIntegers l]
        algebraicCompactCoefficientCompletion ρ p l U m) :=
  congruenceCompletionRepresentation U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun n => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).1)

/-- The actual completed algebraic coefficient action with derived joint continuity. -/
def algebraicCompactCoefficientCompletionContinuousAction :
    ContAction TopCat.{u} (algebraicCompactCongruenceGroupLimit ρ p l U m hm) :=
  congruenceCompletionContinuousAction U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun n => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).1)

end AlgebraicCompact

end Langlands.Shimura.Coefficients
