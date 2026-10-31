import Langlands.AbelianScheme.Tate.WeilRationalFunctorialityStatement
import Langlands.AlgebraicGeometry.Picard.FiniteWeilFunctorialityProof

/-! # Rational dual-homomorphism compatibility of the actual Weil pairing: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
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
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "GB" => dualCommGroupSchemeFromEvaluation B hB preservation MB evaluationB
  stability composition unitCoherence associativity comparison symmetry
local notation "dualMap" => dualCommGroupSchemeMapFromEvaluation preservation composition
  unitCoherence associativity comparison symmetry stability hA hB MA evaluationA MB
  evaluationB
local notation "levelPairA" => finiteWeilLevelBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA
local notation "levelPairB" => finiteWeilLevelBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hB MB evaluationB

/-- Finite-level dual-homomorphism compatibility of the actual Weil pairing on torsion
sections over a test scheme. -/
theorem finiteWeilLevelBilinearMap_levelMap (f : A ⟶ B) (n : ℕ) (T : Over S)
    (x : GroupScheme.Tate.Level A.toGrp T n) (y : GroupScheme.Tate.Level (GB).toGrp T n) :
    levelPairB n T (GroupScheme.Tate.levelMap T (groupHom f) n x) y =
      levelPairA n T x
        (GroupScheme.Tate.levelMap T (CommGroupScheme.groupHom (dualMap f)) n y) := by
  obtain ⟨x, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).surjective x
  obtain ⟨y, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv (GB).toGrp T n).surjective y
  rw [← GroupScheme.Tate.kernelLevelEquiv_map, ← GroupScheme.Tate.kernelLevelEquiv_map,
    finiteWeilLevelBilinearMap_apply, finiteWeilLevelBilinearMap_apply]
  simp only [GroupScheme.Tate.kernelLift, AddEquiv.symm_apply_apply, toMul_ofMul]
  have h := congrArg
    (fun q => prod.lift (x.toMul : T ⟶ (kernelCommGroupScheme (multiplication A (n : ℤ))).X)
      (y.toMul : T ⟶ (GroupScheme.torsion (GB).toGrp (n : ℤ)).X) ≫ q)
    (finiteWeilPairing_dualMap preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f n)
  simp only [prod.lift_map_assoc] at h
  erw [Category.comp_id, Category.comp_id] at h
  exact congrArg (fun z => mu.pointsLevelEquiv n T (Additive.ofMul z)) h

variable (compatibility : RelativeFiniteWeilTransitionStatement.{u}) (T : Over S)
  (P : ℕ → Prop)

local notation "integralPairA" => integralWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T P
local notation "integralPairB" => integralWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hB MB evaluationB compatibility T P
local notation "rationalPairA" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T P
local notation "rationalPairB" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hB MB evaluationB compatibility T P

/-- Integral dual-homomorphism compatibility, coordinatewise in the inverse limit. -/
theorem integralWeilBilinearMap_map (f : A ⟶ B)
    (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral (GB).toGrp T P) :
    integralPairB (GroupScheme.Tate.map T P (groupHom f) x) y =
      integralPairA x (GroupScheme.Tate.map T P (CommGroupScheme.groupHom (dualMap f)) y) := by
  apply Subtype.ext
  funext n
  exact finiteWeilLevelBilinearMap_levelMap preservation composition unitCoherence
    associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB f n.val T
    (x.val n) (y.val n)

/-- Rational dual-homomorphism compatibility for an actual integral homomorphism. -/
theorem rationalWeilBilinearMap_rationalMap (f : A ⟶ B)
    (x : GroupScheme.Tate.Rational A.toGrp T P)
    (y : GroupScheme.Tate.Rational (GB).toGrp T P) :
    rationalPairB (GroupScheme.Tate.rationalMap T P (groupHom f) x) y =
      rationalPairA x
        (GroupScheme.Tate.rationalMap T P (CommGroupScheme.groupHom (dualMap f)) y) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      rw [GroupScheme.Tate.rationalMap_tmul, GroupScheme.Tate.rationalMap_tmul,
        rationalWeilBilinearMap_tmul, rationalWeilBilinearMap_tmul,
        integralWeilBilinearMap_map preservation composition unitCoherence associativity
          comparison symmetry stability hA hB MA evaluationA MB evaluationB compatibility T P]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

variable (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)

/-- Rational dual-homomorphism compatibility for every rational homomorphism, with the
rational dual `dualHom0`. -/
theorem rationalWeilBilinearMap_rationalHomMap (f : Hom0 A B) (x : Tate.Rational A T P)
    (y : Tate.Rational (dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
      evaluationB stability composition unitCoherence associativity comparison symmetry) T P) :
    rationalPairB (Tate.rationalHomMap T P f x) y =
      rationalPairA x (Tate.rationalHomMap T P (dualHom0 preservation composition
        unitCoherence associativity comparison symmetry stability hA hB additivity MA
        evaluationA MB evaluationB geometryA geometryB f) y) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    rw [dualHom0_tmul, Tate.rationalHomMap_tmul, Tate.rationalHomMap_tmul,
      LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, map_smul]
    congr 1
    exact rationalWeilBilinearMap_rationalMap preservation composition unitCoherence
      associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB
      compatibility T P f x y
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

/-- The actual rational Weil pairing is adjoint for a rational homomorphism and its
constructed rational dual. -/
theorem rationalWeilFunctoriality : RationalWeilFunctorialityStatement.{u} := by
  intro preservation composition unitCoherence associativity comparison symmetry stability
    compatibility S _ A B hA hB geometryA geometryB MA evaluationA MB evaluationB additivity
    T P f DB df x y
  exact rationalWeilBilinearMap_rationalHomMap preservation composition unitCoherence
    associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB
    compatibility T P geometryA geometryB additivity f x y

end Langlands.AbelianScheme
