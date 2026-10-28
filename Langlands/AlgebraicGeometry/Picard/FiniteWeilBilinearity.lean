import Langlands.AlgebraicGeometry.Picard.FiniteWeilPairing
import Langlands.AlgebraicGeometry.Picard.DualKernelCharacterAdditivity

/-! # Bilinearity of the actual finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "dualTorsion" n:arg => torsion (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)
local notation "ki" n:arg =>
  relativeDualMultiplicationKernelIso preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA (n : ℤ)
local notation "chi" => dualTorsionCharacter preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "value" => finiteWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "pairing" => finiteWeilPairing preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

/-- Multiplication of actual dual-torsion points adds their intrinsic characters. -/
lemma dualTorsionCharacter_mul (n : ℕ) {T : Over S}
    (y y' : T ⟶ (dualTorsion n).X) :
    chi n (y * y') = chi n y + chi n y' := by
  unfold dualTorsionCharacter
  rw [MonObj.mul_comp]
  exact dualKernelPointCharacter_mul hA stability (multiplication A (n : ℤ)) hA
    preservation composition unitCoherence associativity comparison symmetry
    MA evaluationA MA evaluationA (y ≫ (ki n).inv.hom.hom) (y' ≫ (ki n).inv.hom.hom)

/-- The actual identity of dual torsion gives the zero character. -/
@[simp]
lemma dualTorsionCharacter_one (n : ℕ) (T : Over S) :
    chi n (1 : T ⟶ (dualTorsion n).X) = 0 := by
  unfold dualTorsionCharacter
  rw [MonObj.one_comp]
  exact dualKernelPointCharacter_one hA stability (multiplication A (n : ℤ)) hA
    preservation composition unitCoherence associativity comparison symmetry
    MA evaluationA MA evaluationA T

/-- Intrinsic beta on dual torsion, as an additive homomorphism on every test scheme. -/
def dualTorsionCharacterAddHom (n : ℕ) (T : Over S) :
    Additive (T ⟶ (dualTorsion n).X) →+
      (Cartier.characters (primal n)).obj (op T) where
  toFun y := chi n y.toMul
  map_zero' := dualTorsionCharacter_one preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n T
  map_add' y y' := dualTorsionCharacter_mul preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n y.toMul y'.toMul

/-- Inverting an actual dual-torsion point negates its character. -/
@[simp]
lemma dualTorsionCharacter_inv (n : ℕ) {T : Over S}
    (y : T ⟶ (dualTorsion n).X) :
    chi n y⁻¹ = -chi n y :=
  map_neg (dualTorsionCharacterAddHom preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n T) (Additive.ofMul y)

/-- The intrinsic root-valued evaluation is trivial at the dual identity. -/
@[simp]
lemma finiteWeilValue_one_right (n : ℕ) {T : Over S} (x : T ⟶ (primal n).X) :
    value n x 1 = 1 := by
  unfold finiteWeilValue
  rw [dualTorsionCharacter_one, Cartier.muEvaluation_zero]

/-- Multiplication in actual dual torsion multiplies the intrinsic evaluation. -/
lemma finiteWeilValue_mul_right (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y y' : T ⟶ (dualTorsion n).X) :
    value n x (y * y') = value n x y * value n x y' := by
  unfold finiteWeilValue
  rw [dualTorsionCharacter_mul, Cartier.muEvaluation_add]

/-- Inversion in actual dual torsion inverts the intrinsic evaluation. -/
@[simp]
lemma finiteWeilValue_inv_right (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y : T ⟶ (dualTorsion n).X) :
    value n x y⁻¹ = (value n x y)⁻¹ := by
  unfold finiteWeilValue
  rw [dualTorsionCharacter_inv, Cartier.muEvaluation_neg]

/-- The actual scheme pairing preserves the dual unit on every test scheme. -/
@[simp]
lemma finiteWeilPairing_one_right (n : ℕ) {T : Over S} (x : T ⟶ (primal n).X) :
    prod.lift x (1 : T ⟶ (dualTorsion n).X) ≫ pairing n = 1 := by
  rw [finiteWeilPairing_points, finiteWeilValue_one_right]

/-- The actual scheme pairing is multiplicative in the dual variable on every test scheme. -/
lemma finiteWeilPairing_mul_right (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y y' : T ⟶ (dualTorsion n).X) :
    prod.lift x (y * y') ≫ pairing n =
      (prod.lift x y ≫ pairing n) * (prod.lift x y' ≫ pairing n) := by
  rw [finiteWeilPairing_points, finiteWeilPairing_points, finiteWeilPairing_points,
    finiteWeilValue_mul_right]

/-- The constructed evaluation is additive in both point variables, in additive notation. -/
def finiteWeilBilinearMap (n : ℕ) (T : Over S) :
    Additive (T ⟶ (primal n).X) →+
      Additive (T ⟶ (dualTorsion n).X) →+ Additive (T ⟶ (mu S n).X) where
  toFun x :=
    { toFun y := Additive.ofMul (value n x.toMul y.toMul)
      map_zero' := congrArg Additive.ofMul
        (finiteWeilValue_one_right preservation composition unitCoherence associativity
          comparison symmetry stability hA MA evaluationA n x.toMul)
      map_add' y y' := congrArg Additive.ofMul
        (finiteWeilValue_mul_right preservation composition unitCoherence associativity
          comparison symmetry stability hA MA evaluationA n x.toMul y.toMul y'.toMul) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul
      (finiteWeilValue_one_left preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA n y.toMul)
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul
      (finiteWeilValue_mul_left preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA n x.toMul x'.toMul y.toMul)

end Langlands.AbelianScheme
