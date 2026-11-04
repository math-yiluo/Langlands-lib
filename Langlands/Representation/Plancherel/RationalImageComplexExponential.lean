import Langlands.Representation.Plancherel.RationalImageRealPart
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Complex exponential parameters on the actual rational valuation image -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Complex additive parameters on the actual integer valuation image. -/
abbrev rationalImageComplexFunctionals :=
  Additive (rationalDiscreteValuationImage G) →+ ℂ

/-- The real part of a complex additive parameter, on the same actual image. -/
def rationalImageParameterRealPart (lam : rationalImageComplexFunctionals G) :
    rationalImageRealFunctionals G where
  toFun a := (lam a).re
  map_zero' := by simp
  map_add' a b := by simp

/-- Include a real additive parameter in the complex parameter space. -/
def rationalImageParameterOfReal (phi : rationalImageRealFunctionals G) :
    rationalImageComplexFunctionals G where
  toFun a := (phi a : ℂ)
  map_zero' := by simp
  map_add' a b := by simp

/-- The source's positive period, with its explicit residue-cardinality scale. -/
def rationalImageComplexPeriod : ℂ :=
  (2 * Real.pi * Complex.I) / (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)

/-- Embed the actual integer dual as complex period parameters. -/
def rationalImagePeriodEmbedding :
    (Additive (rationalDiscreteValuationImage G) →+ ℤ) →+
      rationalImageComplexFunctionals G where
  toFun n :=
    { toFun := fun a => rationalImageComplexPeriod (F := F) * (n a : ℂ)
      map_zero' := by simp
      map_add' a b := by simp [mul_add] }
  map_zero' := by ext a; simp
  map_add' n m := by ext a; simp [mul_add]

/-- The period subgroup is the image of the actual integer dual. -/
def rationalImagePeriodLattice : AddSubgroup (rationalImageComplexFunctionals G) :=
  (rationalImagePeriodEmbedding G).range

/-- Exponentiate an additive parameter using the source's `q^(-s)` convention. -/
def rationalImageComplexCharacter (lam : rationalImageComplexFunctionals G) :
    rationalImageCharacters G where
  toFun a := Units.mk0
    (Complex.exp (-lam (Additive.ofMul a) *
      (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)))
    (Complex.exp_ne_zero _)
  map_one' := by apply Units.ext; simp
  map_mul' a b := by
    apply Units.ext
    change Complex.exp (-lam (Additive.ofMul a + Additive.ofMul b) *
      (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) = _
    simp only [map_add, neg_add, add_mul, Complex.exp_add, Units.val_mul,
      Units.val_mk0]
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem rationalImageComplexCharacter_val (lam : rationalImageComplexFunctionals G)
    (a : rationalDiscreteValuationImage G) :
    (rationalImageComplexCharacter G lam a : ℂ) =
      Complex.exp (-lam (Additive.ofMul a) *
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) := rfl

@[simp]
theorem rationalImageComplexCharacter_zero :
    rationalImageComplexCharacter G 0 = 1 := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  simp

theorem rationalImageComplexCharacter_add (lam mu : rationalImageComplexFunctionals G) :
    rationalImageComplexCharacter G (lam + mu) =
      rationalImageComplexCharacter G lam * rationalImageComplexCharacter G mu := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  change Complex.exp (-(lam + mu) (Additive.ofMul a) *
    (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) =
      Complex.exp (-lam (Additive.ofMul a) *
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) *
      Complex.exp (-mu (Additive.ofMul a) *
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ))
  rw [AddMonoidHom.add_apply, neg_add, add_mul, Complex.exp_add]

/-- The complex exponential, as a homomorphism from the additive parameter group. -/
def rationalImageComplexExponential :
    Multiplicative (rationalImageComplexFunctionals G) →* rationalImageCharacters G where
  toFun lam := rationalImageComplexCharacter G lam.toAdd
  map_one' := rationalImageComplexCharacter_zero G
  map_mul' lam mu := rationalImageComplexCharacter_add G lam.toAdd mu.toAdd

/-- Complex exponentiation extends the published positive-character construction. -/
theorem rationalImageComplexCharacter_ofReal (phi : rationalImageRealFunctionals G) :
    rationalImageComplexCharacter G (rationalImageParameterOfReal G phi) =
      rationalImagePositiveCharacter G phi := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  change Complex.exp (-(phi (Additive.ofMul a) : ℂ) *
    (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) =
      (Real.exp (-phi (Additive.ofMul a) *
        Real.log (LocalField.residueCardinality F : ℝ)) : ℂ)
  rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-- The norm of the exponential depends only on the parameter's real part. -/
theorem rationalImageComplexCharacter_norm (lam : rationalImageComplexFunctionals G)
    (a : rationalDiscreteValuationImage G) :
    ‖(rationalImageComplexCharacter G lam a : ℂ)‖ =
      Real.exp (-(lam (Additive.ofMul a)).re *
        Real.log (LocalField.residueCardinality F : ℝ)) := by
  rw [rationalImageComplexCharacter_val, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Taking normalized logarithmic modulus recovers the parameter's real part. -/
@[simp]
theorem rationalImageRealPart_complexCharacter (lam : rationalImageComplexFunctionals G) :
    rationalImageRealPart G (rationalImageComplexCharacter G lam) =
      rationalImageParameterRealPart G lam := by
  apply AddMonoidHom.ext
  intro a
  change -Real.log ‖(rationalImageComplexCharacter G lam a.toMul : ℂ)‖ /
    Real.log (LocalField.residueCardinality F : ℝ) = (lam a).re
  rw [rationalImageComplexCharacter_norm, Real.log_exp, neg_mul, neg_neg]
  exact mul_div_cancel_right₀ _ (Real.log_pos (by
    exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'

/-- Lift each basis value by the principal complex logarithm and extend additively.
The basis is the published basis of the actual image, with finiteness discharged
by connected reductivity. -/
def rationalImageComplexLift (hG : GroupScheme.IsConnectedReductive G)
    (chi : rationalImageCharacters G) : rationalImageComplexFunctionals G :=
  ((rationalReductiveValuationBasis G hG).constr ℤ fun i =>
    -Complex.log (chi ((rationalReductiveValuationBasis G hG i).toMul) : ℂ) /
      (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)).toAddMonoidHom

@[simp]
theorem rationalImageComplexLift_basis (hG : GroupScheme.IsConnectedReductive G)
    (chi : rationalImageCharacters G) (i : Fin (rationalImageRank G)) :
    rationalImageComplexLift G hG chi (rationalReductiveValuationBasis G hG i) =
      -Complex.log (chi ((rationalReductiveValuationBasis G hG i).toMul) : ℂ) /
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ) := by
  change ((rationalReductiveValuationBasis G hG).constr ℤ _)
    (rationalReductiveValuationBasis G hG i) = _
  rw [Module.Basis.constr_basis]

/-- The chosen basis-value lift reconstructs the original actual image character. -/
@[simp]
theorem rationalImageComplexCharacter_lift (hG : GroupScheme.IsConnectedReductive G)
    (chi : rationalImageCharacters G) :
    rationalImageComplexCharacter G (rationalImageComplexLift G hG chi) = chi := by
  let _ := (GroupScheme.rationalCharacterLattice F G hG).2
  apply (rationalImageCharacterCoordinates G (B := ℂˣ)).injective
  funext i
  apply Units.ext
  change Complex.exp (-rationalImageComplexLift G hG chi
    (rationalReductiveValuationBasis G hG i) *
      (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) = _
  rw [rationalImageComplexLift_basis, neg_div, neg_neg,
    div_mul_cancel₀ _ (by
      exact_mod_cast (Real.log_pos (by
        exact_mod_cast LocalField.residueCardinality_gt_one F)).ne')]
  exact Complex.exp_log (Units.ne_zero _)

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalImageComplexExponentialPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The same exponential, pulled back to actual unramified characters of `G(F)`. -/
def rationalCanonicalUnramifiedComplexExponential :
    Multiplicative (rationalImageComplexFunctionals G) →*
      unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  (rationalCanonicalImageUnramifiedContinuousEquiv G).toMulEquiv.toMonoidHom.comp
    (rationalImageComplexExponential G)

@[simp]
theorem rationalCanonicalUnramifiedComplexExponential_val
    (lam : rationalImageComplexFunctionals G) (g : GroupScheme.rationalPoints G) :
    ((rationalCanonicalUnramifiedComplexExponential G
      (Multiplicative.ofAdd lam)).val g : ℂ) =
      Complex.exp (-lam (Additive.ofMul (rationalValuationImageProjection G g)) *
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) := rfl

end CanonicalTopology

end Langlands.Plancherel
