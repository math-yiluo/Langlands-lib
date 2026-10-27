import Langlands.AlgebraicGeometry.Picard.DualKernelCharacter
import Langlands.AlgebraicGeometry.Picard.RelativeDualMultiplication

/-! # Root-valued evaluation of the intrinsic character on actual torsion points -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme

/-- Integer multiplication by `n` is trivial on the actual kernel of `[n]`. -/
lemma torsion_multiplication_eq_one {S : Scheme.{u}}
    (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) :
    multiplication (torsion G n) n = 1 := by
  apply Grp.hom_ext
  apply (cancel_mono (torsionι G n).hom.hom).mp
  change (multiplication (torsion G n) n ≫ torsionι G n).hom.hom = _
  rw [multiplication_naturality]
  change (torsionι G n).hom.hom ≫ (multiplication G n).hom.hom =
    (1 : (torsion G n).X ⟶ (torsion G n).X) ≫ (torsionι G n).hom.hom
  rw [CategoryTheory.MonObj.one_comp]
  exact (kernel_isPullback (multiplication G n)).w

end Langlands.GroupScheme

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
local notation "ki" n:arg =>
  relativeDualMultiplicationKernelIso preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA (n : ℤ)

/-- The actual intrinsic beta character associated to a point of dual `n`-torsion. -/
def dualTorsionCharacter (n : ℕ) {T : Over S}
    (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    (Cartier.characters (primal n)).obj (op T) :=
  dualKernelPointCharacter hA stability (multiplication A (n : ℤ)) hA preservation
    composition unitCoherence associativity comparison symmetry MA evaluationA MA evaluationA
    T (y ≫ (ki n).inv.hom.hom)

/-- Evaluating the actual beta on primal torsion factors canonically through `μ_n`. -/
def finiteWeilValue (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    T ⟶ (mu S n).X :=
  Cartier.muEvaluation n (torsion_multiplication_eq_one A.toGrp (n : ℤ))
    (dualTorsionCharacter preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n y) x

/-- Its inclusion in the multiplicative group is beta evaluated in the source order `x,y`. -/
@[simp]
lemma finiteWeilValue_incl (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA MA evaluationA n x y ≫ (mu.incl S n).toMul.hom.hom =
      Cartier.characterEvaluation
        (dualTorsionCharacter preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n y) x :=
  Cartier.muEvaluation_incl n _ _ x

/-- The actual torsion-kernel universal property uniquely determines this value. -/
lemma finiteWeilValue_unique (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X)
    (z : T ⟶ (mu S n).X)
    (hz : z ≫ (mu.incl S n).toMul.hom.hom =
      Cartier.characterEvaluation
        (dualTorsionCharacter preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n y) x) :
    z = finiteWeilValue preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n x y :=
  Cartier.muEvaluation_unique n _ _ x z hz

@[simp]
lemma finiteWeilValue_one_left (n : ℕ) {T : Over S}
    (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
      stability hA MA evaluationA n 1 y = 1 :=
  Cartier.muEvaluation_one n _ _

/-- Multiplication of primal torsion points multiplies the root-valued evaluation. -/
lemma finiteWeilValue_mul_left (n : ℕ) {T : Over S}
    (x x' : T ⟶ (primal n).X) (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA MA evaluationA n (x * x') y =
      finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
          stability hA MA evaluationA n x y *
        finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
          stability hA MA evaluationA n x' y :=
  Cartier.muEvaluation_mul n _ _ x x'

@[simp]
lemma finiteWeilValue_inv_left (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA MA evaluationA n x⁻¹ y =
      (finiteWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA MA evaluationA n x y)⁻¹ :=
  Cartier.muEvaluation_inv n _ _ x

/-- For each actual dual-torsion point, evaluation is a homomorphism in primal torsion. -/
def finiteWeilValueHom (n : ℕ) {T : Over S}
    (y : T ⟶ (torsion (GA).toGrp (n : ℤ)).X) :
    (T ⟶ (primal n).X) →* (T ⟶ (mu S n).X) where
  toFun x := finiteWeilValue preservation composition unitCoherence associativity comparison
    symmetry stability hA MA evaluationA n x y
  map_one' := finiteWeilValue_one_left preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n y
  map_mul' x x' := finiteWeilValue_mul_left preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n x x' y

end Langlands.AbelianScheme
