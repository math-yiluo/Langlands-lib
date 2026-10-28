import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHom
import Langlands.AlgebraicGeometry.Picard.FiniteWeilBilinearity

/-! # Bilinearity of the finite Weil pairing along an actual homomorphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} {G H : Grp (Over S)}
  [IsCommMonObj G.X] [IsCommMonObj H.X]

/-- The actual torsion-kernel map is additive on points of every test scheme. -/
def kernelLevelMapPointsAddHom (f : G ⟶ H) (n : ℕ) (T : Over S) :
    Additive (T ⟶ (kernel (multiplication G n)).X) →+
      Additive (T ⟶ (kernel (multiplication H n)).X) where
  toFun x := Additive.ofMul (x.toMul ≫ kernelLevelMap f n)
  map_zero' := by
    apply (kernelLevelEquiv H T n).injective
    simp only [kernelLevelEquiv_map, map_zero]
  map_add' x y := by
    apply (kernelLevelEquiv H T n).injective
    simp only [kernelLevelEquiv_map, map_add]

/-- The actual restriction fixes the identity point. -/
@[simp]
lemma kernelLevelMap_comp_one (f : G ⟶ H) (n : ℕ) (T : Over S) :
    (1 : T ⟶ (kernel (multiplication G n)).X) ≫ kernelLevelMap f n = 1 :=
  congrArg Additive.toMul (map_zero (kernelLevelMapPointsAddHom f n T))

/-- The actual restriction preserves the group multiplication on points. -/
lemma kernelLevelMap_comp_mul (f : G ⟶ H) (n : ℕ) {T : Over S}
    (x y : T ⟶ (kernel (multiplication G n)).X) :
    (x * y) ≫ kernelLevelMap f n =
      (x ≫ kernelLevelMap f n) * (y ≫ kernelLevelMap f n) :=
  congrArg Additive.toMul
    (map_add (kernelLevelMapPointsAddHom f n T) (Additive.ofMul x) (Additive.ofMul y))

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "value" => finiteWeilAlongHomValue preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA
local notation "pairing" => finiteWeilAlongHomPairing preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA

/-- Pullback along the actual torsion map preserves the second-variable identity. -/
@[simp]
lemma finiteWeilAlongHomValue_one_right (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) :
    value lam n x 1 = 1 := by
  unfold finiteWeilAlongHomValue finiteWeilAlongHomTorsionMap
  rw [Langlands.GroupScheme.Tate.kernelLevelMap_comp_one, finiteWeilValue_one_right]

/-- Pullback along the actual torsion map preserves second-variable multiplication. -/
lemma finiteWeilAlongHomValue_mul_right (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y y' : T ⟶ (primal n).X) :
    value lam n x (y * y') = value lam n x y * value lam n x y' := by
  unfold finiteWeilAlongHomValue finiteWeilAlongHomTorsionMap
  rw [Langlands.GroupScheme.Tate.kernelLevelMap_comp_mul, finiteWeilValue_mul_right]

/-- The same root-valued pairing is an additive homomorphism in both point variables. -/
def finiteWeilAlongHomBilinearMap (lam : A ⟶ DA) (n : ℕ) (T : Over S) :
    Additive (T ⟶ (primal n).X) →+
      Additive (T ⟶ (primal n).X) →+ Additive (T ⟶ (mu S n).X) where
  toFun x :=
    { toFun y := Additive.ofMul (value lam n x.toMul y.toMul)
      map_zero' := congrArg Additive.ofMul
        (finiteWeilAlongHomValue_one_right preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA lam n x.toMul)
      map_add' y y' := congrArg Additive.ofMul
        (finiteWeilAlongHomValue_mul_right preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA lam n
          x.toMul y.toMul y'.toMul) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul
      (map_one (finiteWeilAlongHomValueHom preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA lam n y.toMul))
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul
      (map_mul (finiteWeilAlongHomValueHom preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA lam n y.toMul)
        x.toMul x'.toMul)

/-- The bundled bilinear map evaluates the original product-scheme morphism. -/
@[simp]
lemma finiteWeilAlongHomBilinearMap_apply (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y : Additive (T ⟶ (primal n).X)) :
    (finiteWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA lam n T x y).toMul =
      prod.lift x.toMul y.toMul ≫ pairing lam n := by
  exact (finiteWeilAlongHomPairing_points preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA lam n
    x.toMul y.toMul).symm

/-- The product-scheme pairing preserves the second identity on every test scheme. -/
@[simp]
lemma finiteWeilAlongHomPairing_one_right (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x : T ⟶ (primal n).X) :
    prod.lift x (1 : T ⟶ (primal n).X) ≫ pairing lam n = 1 := by
  rw [finiteWeilAlongHomPairing_points, finiteWeilAlongHomValue_one_right]

/-- The product-scheme pairing preserves second-variable multiplication on all points. -/
lemma finiteWeilAlongHomPairing_mul_right (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y y' : T ⟶ (primal n).X) :
    prod.lift x (y * y') ≫ pairing lam n =
      (prod.lift x y ≫ pairing lam n) * (prod.lift x y' ≫ pairing lam n) := by
  rw [finiteWeilAlongHomPairing_points, finiteWeilAlongHomPairing_points,
    finiteWeilAlongHomPairing_points, finiteWeilAlongHomValue_mul_right]

end Langlands.AbelianScheme
