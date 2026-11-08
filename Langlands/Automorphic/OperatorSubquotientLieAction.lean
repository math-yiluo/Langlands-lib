import Langlands.Automorphic.OperatorSubquotientArchimedean
import Langlands.Automorphic.PlaceLieAction
import Langlands.Global.ArchimedeanPlaceAdjoint

/-! # Actual complex Lie actions on automorphic operator quotients -/

noncomputable section
universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance quotientLieRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientLieContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientLieSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientLieFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientLieStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientLieRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The genuine complex Lie algebra acts through the quotient's induced enveloping action. -/
def complexLieAction : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ Q.Space :=
  Q.envelopingAction.toLieHom.comp (envelopingGenerator F n)

@[simp] theorem complexLieAction_apply (X : ComplexLieAlgebra F n) (f : Q.Space) :
    Q.complexLieAction X f = Q.envelopingAction (envelopingGenerator F n X) f := rfl

/-- Restrict the same action along the actual complexified compact Lie inclusion. -/
def compactLieAction : CompactComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ Q.Space :=
  Q.complexLieAction.comp (compactComplexInclusion F n)

theorem compactLieAction_apply (X : CompactComplexLieAlgebra F n) (f : Q.Space) :
    Q.compactLieAction X f = Q.complexLieAction (compactComplexInclusion F n X) f := rfl

instance quotientComplexLieRingModule : LieRingModule (ComplexLieAlgebra F n) Q.Space :=
  LieRingModule.compLieHom Q.Space Q.complexLieAction

instance quotientComplexLieModule : LieModule ℂ (ComplexLieAlgebra F n) Q.Space :=
  LieModule.compLieHom Q.Space Q.complexLieAction

instance quotientCompactLieRingModule :
    LieRingModule (CompactComplexLieAlgebra F n) Q.Space :=
  LieRingModule.compLieHom Q.Space (compactComplexInclusion F n)

instance quotientCompactLieModule : LieModule ℂ (CompactComplexLieAlgebra F n) Q.Space :=
  LieModule.compLieHom Q.Space (compactComplexInclusion F n)

@[simp] theorem complex_lie_eq (X : ComplexLieAlgebra F n) (f : Q.Space) :
    ⁅X, f⁆ = Q.complexLieAction X f := rfl

@[simp] theorem compact_lie_eq (X : CompactComplexLieAlgebra F n) (f : Q.Space) :
    ⁅X, f⁆ = Q.compactLieAction X f := rfl

/-- On a projected representative the quotient operator is the projected numerator operator. -/
@[simp] theorem complexLieAction_projection (X : ComplexLieAlgebra F n) (f : Q.upper.Space) :
    Q.complexLieAction X (Q.projection f) = Q.projection (Q.upper.complexLieAction X f) := rfl

@[simp] theorem compactLieAction_projection (X : CompactComplexLieAlgebra F n)
    (f : Q.upper.Space) :
    Q.compactLieAction X (Q.projection f) = Q.projection (Q.upper.compactLieAction X f) := rfl

/-- The canonical projection is a map of complex Lie modules. -/
def complexLieProjection : Q.upper.Space →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ Q.Space where
  toLinearMap := Q.projection.toLinearMap
  map_lie' := rfl

/-- The same projection is a map of compact Lie modules. -/
def compactLieProjection : Q.upper.Space →ₗ⁅ℂ, CompactComplexLieAlgebra F n⁆ Q.Space where
  toLinearMap := Q.projection.toLinearMap
  map_lie' := rfl

@[simp] theorem complexLieProjection_apply (f : Q.upper.Space) :
    Q.complexLieProjection f = Q.projection f := rfl

@[simp] theorem compactLieProjection_apply (f : Q.upper.Space) :
    Q.compactLieProjection f = Q.projection f := rfl

theorem complexLieProjection_surjective : Function.Surjective Q.complexLieProjection :=
  Q.projection_surjective

theorem compactLieProjection_surjective : Function.Surjective Q.compactLieProjection :=
  Q.projection_surjective

/-- The actual denominator is a complex Lie submodule of the numerator. -/
def lowerComplexLieSubmodule : LieSubmodule ℂ (ComplexLieAlgebra F n) Q.upper.Space :=
  { Q.lower.toSubmodule with
    lie_mem := fun {X} {_} hf =>
      Q.lower.apply_mem_toSubmodule (differentialOperator F n (envelopingGenerator F n X)) hf }

/-- The same denominator is a compact Lie submodule. -/
def lowerCompactLieSubmodule : LieSubmodule ℂ (CompactComplexLieAlgebra F n) Q.upper.Space :=
  { Q.lower.toSubmodule with
    lie_mem := fun {X} {_} hf =>
      Q.lower.apply_mem_toSubmodule
        (differentialOperator F n (envelopingGenerator F n (compactComplexInclusion F n X))) hf }

@[simp] theorem mem_lowerComplexLieSubmodule (f : Q.upper.Space) :
    f ∈ Q.lowerComplexLieSubmodule ↔ f ∈ Q.lower := Iff.rfl

@[simp] theorem mem_lowerCompactLieSubmodule (f : Q.upper.Space) :
    f ∈ Q.lowerCompactLieSubmodule ↔ f ∈ Q.lower := Iff.rfl

/-- The kernel of the Lie projection is exactly the actual denominator. -/
theorem complexLieProjection_ker : Q.complexLieProjection.ker = Q.lowerComplexLieSubmodule := by
  ext f
  exact Q.projection_eq_zero_iff f

theorem compactLieProjection_ker : Q.compactLieProjection.ker = Q.lowerCompactLieSubmodule := by
  ext f
  exact Q.projection_eq_zero_iff f

/-- The actual quotient is Mathlib's Lie module quotient by the actual denominator. -/
def complexLieQuotientEquiv :
    Q.Space ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (Q.upper.Space ⧸ Q.lowerComplexLieSubmodule) :=
  { Submodule.quotEquivOfEq Q.lower.toSubmodule Q.lowerComplexLieSubmodule.toSubmodule rfl with
    map_lie' := fun {X} {f} => by
      induction f using Submodule.Quotient.induction_on with
      | H g => exact ((LieSubmodule.Quotient.mk' Q.lowerComplexLieSubmodule).map_lie X g).symm }

/-- The same identification for the compact Lie module structures. -/
def compactLieQuotientEquiv :
    Q.Space ≃ₗ⁅ℂ, CompactComplexLieAlgebra F n⁆ (Q.upper.Space ⧸ Q.lowerCompactLieSubmodule) :=
  { Submodule.quotEquivOfEq Q.lower.toSubmodule Q.lowerCompactLieSubmodule.toSubmodule rfl with
    map_lie' := fun {X} {f} => by
      induction f using Submodule.Quotient.induction_on with
      | H g => exact ((LieSubmodule.Quotient.mk' Q.lowerCompactLieSubmodule).map_lie X g).symm }

theorem complexLieQuotientEquiv_projection (f : Q.upper.Space) :
    Q.complexLieQuotientEquiv (Q.projection f) =
      LieSubmodule.Quotient.mk' Q.lowerComplexLieSubmodule f := rfl

theorem compactLieQuotientEquiv_projection (f : Q.upper.Space) :
    Q.compactLieQuotientEquiv (Q.projection f) =
      LieSubmodule.Quotient.mk' Q.lowerCompactLieSubmodule f := rfl

/-- Finite adelic translations commute with the induced complex Lie action. -/
theorem finiteRepresentation_complexLieAction (d : FiniteAdelicGL F n)
    (X : ComplexLieAlgebra F n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.complexLieAction X f) =
      Q.complexLieAction X (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (envelopingGenerator F n X) f

theorem finiteRepresentation_compactLieAction (d : FiniteAdelicGL F n)
    (X : CompactComplexLieAlgebra F n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.compactLieAction X f) =
      Q.compactLieAction X (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_complexLieAction d (compactComplexInclusion F n X) f

/-- Compact translation acts on the quotient Lie operators by the actual adjoint. -/
theorem compactRepresentation_complexLieAction (k : standardInfiniteCompact F n)
    (X : ComplexLieAlgebra F n) (f : Q.Space) :
    Q.compactRepresentation k (Q.complexLieAction X f) =
      Q.complexLieAction (complexLieConjugation F n k.val X) (Q.compactRepresentation k f) :=
  (Q.compactRepresentation_envelopingAction k (envelopingGenerator F n X) f).trans
    (congrArg (fun a : EnvelopingAlgebra F n => Q.envelopingAction a (Q.compactRepresentation k f))
      (envelopingConjugation_generator F n k.val X))

/-! ## Archimedean places -/

/-- Restrict the quotient's genuine differential to a complexified real-place Lie algebra. -/
def realPlaceLieAction (v : RP) : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ Q.Space :=
  Q.complexLieAction.comp (realPlaceComplexLieInclusion F n v)

/-- At a complex place the entire underlying real matrix Lie algebra is complexified. -/
def complexPlaceLieAction (v : CP) : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ Q.Space :=
  Q.complexLieAction.comp (complexPlaceComplexLieInclusion F n v)

theorem realPlaceLieAction_apply (v : RP) (X : ℂ ⊗[ℝ] RM) (f : Q.Space) :
    Q.realPlaceLieAction v X f =
      Q.envelopingAction (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) f :=
  rfl

theorem complexPlaceLieAction_apply (v : CP) (X : ℂ ⊗[ℝ] CM) (f : Q.Space) :
    Q.complexPlaceLieAction v X f =
      Q.envelopingAction
        (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) f := rfl

@[simp] theorem realPlaceLieAction_projection (v : RP) (X : ℂ ⊗[ℝ] RM) (f : Q.upper.Space) :
    Q.realPlaceLieAction v X (Q.projection f) =
      Q.projection (Q.upper.realPlaceLieAction v X f) := rfl

@[simp] theorem complexPlaceLieAction_projection (v : CP) (X : ℂ ⊗[ℝ] CM)
    (f : Q.upper.Space) :
    Q.complexPlaceLieAction v X (Q.projection f) =
      Q.projection (Q.upper.complexPlaceLieAction v X f) := rfl

theorem finiteRepresentation_realPlaceLieAction (d : FiniteAdelicGL F n)
    (v : RP) (X : ℂ ⊗[ℝ] RM) (f : Q.Space) :
    Q.finiteRepresentation d (Q.realPlaceLieAction v X f) =
      Q.realPlaceLieAction v X (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_complexLieAction d (realPlaceComplexLieInclusion F n v X) f

theorem finiteRepresentation_complexPlaceLieAction (d : FiniteAdelicGL F n)
    (v : CP) (X : ℂ ⊗[ℝ] CM) (f : Q.Space) :
    Q.finiteRepresentation d (Q.complexPlaceLieAction v X f) =
      Q.complexPlaceLieAction v X (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_complexLieAction d (complexPlaceComplexLieInclusion F n v X) f

/-- The global quotient operator of every real generator is the sum of its place operators. -/
theorem complexify_action_eq_sum_place (X : RealLieAlgebra F n) (f : Q.Space) :
    Q.complexLieAction (complexify F n X) f =
      (∑ v : RP, Q.realPlaceLieAction v
        ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) +
      (∑ v : CP, Q.complexPlaceLieAction v
        ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X) f) := by
  have h := congrArg (fun Y : RealLieAlgebra F n =>
    Q.complexLieAction (complexify F n Y) f) (sum_placeLieInclusions F n X).symm
  simpa only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
    realPlaceLieAction, complexPlaceLieAction, LieHom.comp_apply,
    realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul,
    complexify_apply] using h

/-- Full compact translation acts on each real-place quotient operator by its matrix adjoint. -/
theorem compactRepresentation_realPlaceLieAction (p : ArchimedeanCompactFactors F n)
    (v : RP) (X : ℂ ⊗[ℝ] RM) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realPlaceLieAction v X f) =
      Q.realPlaceLieAction v (unitaryMatrixComplexLieConjugation ℝ n (p.1 v) X)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) :=
  (Q.compactRepresentation_complexLieAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlaceComplexLieInclusion F n v X) f).trans
      (congrArg (fun Y : ComplexLieAlgebra F n =>
        Q.complexLieAction Y
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (complexLieConjugation_realInclusion F n p v X))

theorem compactRepresentation_complexPlaceLieAction (p : ArchimedeanCompactFactors F n)
    (v : CP) (X : ℂ ⊗[ℝ] CM) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.complexPlaceLieAction v X f) =
      Q.complexPlaceLieAction v (unitaryMatrixComplexLieConjugation ℂ n (p.2 v) X)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) :=
  (Q.compactRepresentation_complexLieAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlaceComplexLieInclusion F n v X) f).trans
      (congrArg (fun Y : ComplexLieAlgebra F n =>
        Q.complexLieAction Y
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (complexLieConjugation_complexInclusion F n p v X))

namespace Equivalence

variable {Q T : OperatorSubquotient F n}

/-- A quotient equivalence retains the actual complex Lie module on the same vectors. -/
def complexLieRestriction (e : Q.Equivalence T) :
    Q.Space ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ T.Space :=
  { e.toLinearEquiv with
    map_lie' := fun {X} {f} => LinearMap.congr_fun
      (e.toIntertwiningMap.isIntertwining' (differentialOperator F n (envelopingGenerator F n X)))
      f }

/-- The same equivalence retains the actual compact Lie module. -/
def compactLieRestriction (e : Q.Equivalence T) :
    Q.Space ≃ₗ⁅ℂ, CompactComplexLieAlgebra F n⁆ T.Space :=
  { e.toLinearEquiv with
    map_lie' := fun {X} {f} => LinearMap.congr_fun
      (e.toIntertwiningMap.isIntertwining'
        (differentialOperator F n (envelopingGenerator F n (compactComplexInclusion F n X)))) f }

@[simp] theorem complexLieRestriction_apply (e : Q.Equivalence T) (f : Q.Space) :
    e.complexLieRestriction f = e f := rfl

@[simp] theorem compactLieRestriction_apply (e : Q.Equivalence T) (f : Q.Space) :
    e.compactLieRestriction f = e f := rfl

/-- The original equivalence intertwines every actual real-place quotient operator. -/
theorem map_realPlaceLieAction (e : Q.Equivalence T) (v : RP) (X : ℂ ⊗[ℝ] RM)
    (f : Q.Space) :
    e (Q.realPlaceLieAction v X f) = T.realPlaceLieAction v X (e f) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining'
    (differentialOperator F n (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)))) f

theorem map_complexPlaceLieAction (e : Q.Equivalence T) (v : CP) (X : ℂ ⊗[ℝ] CM)
    (f : Q.Space) :
    e (Q.complexPlaceLieAction v X f) = T.complexPlaceLieAction v X (e f) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining'
    (differentialOperator F n
      (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)))) f

end Equivalence
end OperatorSubquotient
end Langlands.Automorphic
