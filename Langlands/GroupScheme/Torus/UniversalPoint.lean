import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Lie.DualNumberKernel
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Universal points of split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {R : CommRingCat.{u}} (I : Type u) [Finite I]
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The unit coordinates of a split-torus point over a test algebra. -/
abbrev algebraPointsEquiv (A : Type u) [CommRing A] [Algebra R A] :
    Lie.AffinePoints (splitTorus (Spec R) I) A ≃* (I → Aˣ) :=
  affinePointsEquiv I ((algSpec R).obj (op (CommAlgCat.of R A))).hom

/-- Unit coordinates commute with change of test algebra. -/
theorem algebraPointsEquiv_naturality (f : A →ₐ[R] B)
    (t : Lie.AffinePoints (splitTorus (Spec R) I) A) :
    algebraPointsEquiv I B (Lie.affineMap _ f t) =
      fun i => Units.map f.toMonoidHom (algebraPointsEquiv I A t i) := by
  funext i
  change Gm.affinePointsEquiv _
    (((algSpec R).map (CommAlgCat.ofHom f).op ≫ t) ≫ _) = _
  rw [Category.assoc]
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality]
  change ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom) _ =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

variable [DecidableEq I]

/-- The unit monomial indexed by an exponent vector. -/
def exponentUnit (m : I → ℤ) : (AddMonoidAlgebra R (I → ℤ))ˣ :=
  (AddMonoidAlgebra.of R (I → ℤ)).toHomUnits (Multiplicative.ofAdd m)

omit [Finite I] [DecidableEq I] in
@[simp] theorem exponentUnit_val (m : I → ℤ) :
    (exponentUnit (R := R) I m : AddMonoidAlgebra R (I → ℤ)) =
      AddMonoidAlgebra.single m 1 := rfl

/-- The point with coordinates the independent invertible monomials. -/
def universalPoint : Lie.AffinePoints (splitTorus (Spec R) I)
    (AddMonoidAlgebra R (I → ℤ)) :=
  (algebraPointsEquiv I _).symm (fun i => exponentUnit I (Pi.single i 1))

@[simp] theorem algebraPointsEquiv_universalPoint :
    algebraPointsEquiv I _ (universalPoint (R := R) I) =
      fun i => exponentUnit I (Pi.single i 1) :=
  MulEquiv.apply_symm_apply _ _

variable [Fintype I]

/-- Evaluate an exponent vector at a family of units. -/
def exponentValue (t : I → Aˣ) : Multiplicative (I → ℤ) →* Aˣ where
  toFun m := ∏ i, t i ^ m.toAdd i
  map_one' := by simp
  map_mul' m n := by
    change (∏ i, t i ^ (m.toAdd i + n.toAdd i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]

omit [Finite I] in
@[simp] theorem exponentValue_single (t : I → Aˣ) (i : I) :
    exponentValue I t (Multiplicative.ofAdd (Pi.single i 1)) = t i := by
  classical
  simp [exponentValue, Pi.single_apply]

/-- The algebra map evaluating all monomials at the specified units. -/
def evaluateUnits (t : I → Aˣ) : AddMonoidAlgebra R (I → ℤ) →ₐ[R] A :=
  AddMonoidAlgebra.lift R A (I → ℤ) ((Units.coeHom A).comp (exponentValue I t))

omit [Finite I] [DecidableEq I] in
@[simp] theorem evaluateUnits_single (t : I → Aˣ) (m : I → ℤ) (r : R) :
    evaluateUnits I t (AddMonoidAlgebra.single m r) =
      algebraMap R A r * (exponentValue I t (Multiplicative.ofAdd m) : A) := by
  simp [evaluateUnits, Algebra.smul_def]

/-- Every algebra-valued point is an evaluation of the universal point. -/
theorem universalPoint_evaluateUnits (t : I → Aˣ) :
    Lie.affineMap _ (evaluateUnits (R := R) I t) (universalPoint (R := R) I) =
      (algebraPointsEquiv I A).symm t := by
  apply (algebraPointsEquiv I A).injective
  rw [algebraPointsEquiv_naturality, algebraPointsEquiv_universalPoint,
    MulEquiv.apply_symm_apply]
  funext i
  apply Units.ext
  change evaluateUnits I t (AddMonoidAlgebra.single (Pi.single i 1) 1) = (t i : A)
  simp

end Langlands.GroupScheme.splitTorus
