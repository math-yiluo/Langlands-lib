import Langlands.AlgebraicGeometry.Picard.FiniteWeilEvaluation
import Langlands.AlgebraicGeometry.Picard.DualKernelCharacterNaturality

/-! # The actual product-scheme map underlying finite Weil evaluation -/

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

/-- The character attached to actual dual torsion is natural in the test scheme. -/
lemma dualTorsionCharacter_restrict (n : ℕ) {T U : Over S} (b : U ⟶ T)
    (y : T ⟶ (dualTorsion n).X) :
    dualTorsionCharacter preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n (b ≫ y) =
      (Cartier.characters (primal n)).map b.op
        (dualTorsionCharacter preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n y) := by
  unfold dualTorsionCharacter
  rw [Category.assoc]
  exact dualKernelPointCharacter_restrict hA stability (multiplication A (n : ℤ)) hA b
    preservation composition unitCoherence associativity comparison symmetry
    MA evaluationA MA evaluationA (y ≫ (ki n).inv.hom.hom)

/-- Actual root-valued evaluation commutes with every change of test scheme. -/
lemma finiteWeilValue_restrict (n : ℕ) {T U : Over S} (b : U ⟶ T)
    (x : T ⟶ (primal n).X) (y : T ⟶ (dualTorsion n).X) :
    finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA MA evaluationA n (b ≫ x) (b ≫ y) =
      b ≫ finiteWeilValue preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n x y := by
  unfold finiteWeilValue
  rw [dualTorsionCharacter_restrict]
  exact Cartier.muEvaluation_restrict n _ b _ x

/-- Evaluation on the universal pair gives an actual morphism of schemes over `S`. -/
def finiteWeilPairing (n : ℕ) :
    (primal n).X ⨯ (dualTorsion n).X ⟶ (mu S n).X :=
  finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
    stability hA MA evaluationA n prod.fst prod.snd

/-- Every scheme-valued point of this morphism is the constructed beta evaluation. -/
@[simp]
lemma finiteWeilPairing_points (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y : T ⟶ (dualTorsion n).X) :
    prod.lift x y ≫ finiteWeilPairing preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA n =
      finiteWeilValue preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n x y := by
  simpa only [finiteWeilPairing, prod.lift_fst, prod.lift_snd] using
    (finiteWeilValue_restrict preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n (prod.lift x y) prod.fst prod.snd).symm

/-- The actual evaluation on all test schemes uniquely specifies the scheme morphism. -/
lemma finiteWeilPairing_unique (n : ℕ)
    (q : (primal n).X ⨯ (dualTorsion n).X ⟶ (mu S n).X)
    (hq : ∀ (T : Over S) (x : T ⟶ (primal n).X) (y : T ⟶ (dualTorsion n).X),
      prod.lift x y ≫ q =
        finiteWeilValue preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n x y) :
    q = finiteWeilPairing preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n := by
  simpa only [finiteWeilPairing, prod.lift_fst_snd, Category.id_comp] using
    hq _ prod.fst prod.snd

/-- The product-scheme morphism preserves the unit in its primal variable on all points. -/
@[simp]
lemma finiteWeilPairing_one_left (n : ℕ) {T : Over S}
    (y : T ⟶ (dualTorsion n).X) :
    prod.lift (1 : T ⟶ (primal n).X) y ≫
      finiteWeilPairing preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n = 1 := by
  rw [finiteWeilPairing_points, finiteWeilValue_one_left]

/-- The product-scheme morphism is multiplicative in the primal variable on all points. -/
lemma finiteWeilPairing_mul_left (n : ℕ) {T : Over S}
    (x x' : T ⟶ (primal n).X) (y : T ⟶ (dualTorsion n).X) :
    prod.lift (x * x') y ≫ finiteWeilPairing preservation composition unitCoherence
        associativity comparison symmetry stability hA MA evaluationA n =
      (prod.lift x y ≫ finiteWeilPairing preservation composition unitCoherence
        associativity comparison symmetry stability hA MA evaluationA n) *
      (prod.lift x' y ≫ finiteWeilPairing preservation composition unitCoherence
        associativity comparison symmetry stability hA MA evaluationA n) := by
  rw [finiteWeilPairing_points, finiteWeilPairing_points, finiteWeilPairing_points,
    finiteWeilValue_mul_left]

end Langlands.AbelianScheme
