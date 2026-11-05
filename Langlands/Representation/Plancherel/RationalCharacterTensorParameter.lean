import Langlands.Representation.Plancherel.RationalImageComplexExponential
import Langlands.Representation.Plancherel.RationalImageLattice
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! # Rational-character tensors and the actual complex exponential -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Evaluate a rational algebraic character on the actual integer valuation image,
then include its integer value in the complex numbers. -/
def rationalCharacterImageComplexFunctional :
    GroupScheme.rationalCharacters G →ₗ[ℤ] rationalImageComplexFunctionals G :=
  (show GroupScheme.rationalCharacters G →+ rationalImageComplexFunctionals G from
    { toFun := fun chi =>
        { toFun := fun a => (rationalImageIntegerDual G a chi : ℂ)
          map_zero' := by simp
          map_add' := fun a b => by simp }
      map_zero' := by ext a; simp
      map_add' := fun chi psi => by ext a; simp }).toIntLinearMap

@[simp]
theorem rationalCharacterImageComplexFunctional_apply
    (chi : GroupScheme.rationalCharacters G) (a : rationalDiscreteValuationImage G) :
    rationalCharacterImageComplexFunctional G chi (Additive.ofMul a) =
      (a.val.toAdd chi : ℂ) := rfl

/-- Canonical complex scalar extension of rational-character evaluation on the
actual valuation image. Scalars are the first tensor factor. -/
def rationalCharacterTensorParameter :
    ℂ ⊗[ℤ] GroupScheme.rationalCharacters G →ₗ[ℂ]
      rationalImageComplexFunctionals G :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ
      (GroupScheme.rationalCharacters G →ₗ[ℤ] rationalImageComplexFunctionals G)
      (rationalCharacterImageComplexFunctional G))

@[simp]
theorem rationalCharacterTensorParameter_tmul_apply
    (s : ℂ) (chi : GroupScheme.rationalCharacters G)
    (a : rationalDiscreteValuationImage G) :
    rationalCharacterTensorParameter G (s ⊗ₜ[ℤ] chi) (Additive.ofMul a) =
      s * (a.val.toAdd chi : ℂ) := rfl

/-- The tensor exponential on the actual valuation image. -/
def rationalCharacterTensorExponential :
    Multiplicative (ℂ ⊗[ℤ] GroupScheme.rationalCharacters G) →*
      rationalImageCharacters G :=
  (rationalImageComplexExponential G).comp
    (rationalCharacterTensorParameter G).toAddMonoidHom.toMultiplicative

@[simp]
theorem rationalCharacterTensorExponential_tmul_val
    (s : ℂ) (chi : GroupScheme.rationalCharacters G)
    (a : rationalDiscreteValuationImage G) :
    (rationalCharacterTensorExponential G (Multiplicative.ofAdd (s ⊗ₜ[ℤ] chi)) a : ℂ) =
      Complex.exp (-(s * (a.val.toAdd chi : ℂ)) *
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) := rfl

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalCharacterTensorPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The tensor exponential pulled back to canonical unramified characters of
actual rational points. -/
def rationalCanonicalCharacterTensorExponential :
    Multiplicative (ℂ ⊗[ℤ] GroupScheme.rationalCharacters G) →*
      unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  (rationalCanonicalUnramifiedComplexExponential G).comp
    (rationalCharacterTensorParameter G).toAddMonoidHom.toMultiplicative

/-- Renard's pure-tensor formula, with the actual residue-normalized absolute
value of the actual rational-character evaluation. -/
theorem rationalCanonicalCharacterTensorExponential_tmul_val
    (s : ℂ) (chi : GroupScheme.rationalCharacters G)
    (g : GroupScheme.rationalPoints G) :
    ((rationalCanonicalCharacterTensorExponential G
      (Multiplicative.ofAdd (s ⊗ₜ[ℤ] chi))).val g : ℂ) =
        (LocalField.residueNormalizedAbsoluteValue F
          (GroupScheme.rationalCharacterEval chi g : F) : ℂ) ^ s := by
  have hq : (0 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (LocalField.residueCardinality_gt_one F))
  have hval := fieldNormUnits_rpow F (GroupScheme.rationalCharacterEval chi g)
  change (LocalField.residueCardinality F : ℝ) ^
    (-((rationalCharacterValuation G g).toAdd chi : ℝ)) =
      LocalField.residueNormalizedAbsoluteValue F
        (GroupScheme.rationalCharacterEval chi g : F) at hval
  have habs : 0 < LocalField.residueNormalizedAbsoluteValue F
      (GroupScheme.rationalCharacterEval chi g : F) :=
    hval ▸ Real.rpow_pos_of_pos hq _
  have hlog : Real.log (LocalField.residueNormalizedAbsoluteValue F
      (GroupScheme.rationalCharacterEval chi g : F)) =
        -((rationalCharacterValuation G g).toAdd chi : ℝ) *
          Real.log (LocalField.residueCardinality F : ℝ) := by
    rw [← hval, Real.log_rpow hq]
  change Complex.exp (-(s * ((rationalCharacterValuation G g).toAdd chi : ℂ)) *
    (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) = _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast habs.ne') s,
    ← Complex.ofReal_log habs.le, hlog]
  congr 1
  push_cast
  ring

end CanonicalTopology

end Langlands.Plancherel
