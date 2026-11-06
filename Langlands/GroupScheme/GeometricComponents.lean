import Langlands.GroupScheme.ComponentGaloisContinuityProof
import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-! # Chosen geometric components with their continuous absolute Galois action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k : Type u) [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- All actual components after base change to Mathlib's chosen algebraic closure. -/
def GeometricComponents :=
  AlgebraicallyClosedComponents (baseChanged k (AlgebraicClosure k) H)

/-- The topology is the connected-component quotient topology of the actual base change. -/
instance geometricComponentTopologicalSpace : TopologicalSpace (GeometricComponents k H) :=
  inferInstanceAs (TopologicalSpace
    (AlgebraicallyClosedComponents (baseChanged k (AlgebraicClosure k) H)))

instance geometricComponentT1Space : T1Space (GeometricComponents k H) :=
  inferInstanceAs (T1Space
    (AlgebraicallyClosedComponents (baseChanged k (AlgebraicClosure k) H)))

variable [Smooth H.X.hom] [IsAffineHom H.X.hom]

instance : Group (GeometricComponents k H) :=
  inferInstanceAs (Group
    (AlgebraicallyClosedComponents (baseChanged k (AlgebraicClosure k) H)))

instance : Finite (GeometricComponents k H) :=
  inferInstanceAs (Finite
    (AlgebraicallyClosedComponents (baseChanged k (AlgebraicClosure k) H)))

instance geometricComponentDiscreteTopology : DiscreteTopology (GeometricComponents k H) :=
  inferInstanceAs (DiscreteTopology
    (AlgebraicallyClosedComponents (baseChanged k (AlgebraicClosure k) H)))

/-- An actual algebraic-closure section maps to its geometric component. -/
def geometricComponentOfPoint :
    rationalPoints (baseChanged k (AlgebraicClosure k) H) →* GeometricComponents k H :=
  allComponentOfPoint _

theorem geometricComponentOfPoint_surjective :
    Function.Surjective (geometricComponentOfPoint k H) :=
  allComponentOfPoint_surjective _

/-- The absolute Galois group acts by the actual coefficient automorphisms. -/
def geometricComponentGaloisAction :
    Field.absoluteGaloisGroup k →* MulAut (GeometricComponents k H) :=
  allComponentGaloisAction k (AlgebraicClosure k) H

instance geometricComponentMulDistribMulAction :
    MulDistribMulAction (Field.absoluteGaloisGroup k) (GeometricComponents k H) where
  smul σ c := geometricComponentGaloisAction k H σ c
  one_smul c := by
    change geometricComponentGaloisAction k H 1 c = c
    rw [map_one]
    rfl
  mul_smul σ τ c := by
    change geometricComponentGaloisAction k H (σ * τ) c =
      geometricComponentGaloisAction k H σ (geometricComponentGaloisAction k H τ c)
    rw [map_mul]
    rfl
  smul_one σ := (geometricComponentGaloisAction k H σ).map_one
  smul_mul σ c d := (geometricComponentGaloisAction k H σ).map_mul c d

/-- The scalar action is the semilinear permutation of actual scheme components. -/
theorem geometricComponent_smul (σ : Field.absoluteGaloisGroup k)
    (c : GeometricComponents k H) :
    σ • c = coefficientComponents k (AlgebraicClosure k) H σ c :=
  allComponentConjugate_apply k (AlgebraicClosure k) H σ c

/-- The actual component quotient topology makes the absolute Galois action continuous. -/
instance geometricComponentContinuousSMul :
    ContinuousSMul (Field.absoluteGaloisGroup k) (GeometricComponents k H) where
  continuous_smul := allComponentGaloisAction_continuous k (AlgebraicClosure k) H

/-- On sections the component action is ordinary coefficient conjugation. -/
theorem geometricComponent_smul_ofPoint (σ : Field.absoluteGaloisGroup k)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    σ • geometricComponentOfPoint k H x =
      geometricComponentOfPoint k H (rationalConjugate k (AlgebraicClosure k) H σ x) := by
  rw [geometricComponent_smul]
  exact coefficientComponents_pointComponent k (AlgebraicClosure k) H σ x

variable {H}
  {H' H'' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]
  [Smooth H''.X.hom] [IsAffineHom H''.X.hom]

/-- A homomorphism over k induces the actual map on chosen geometric components. -/
def geometricComponentMap (f : H ⟶ H') :
    GeometricComponents k H →* GeometricComponents k H' :=
  allComponentMap ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map f)

/-- This is exactly the continuous component map of the pulled-back scheme morphism. -/
theorem geometricComponentMap_apply (f : H ⟶ H') (c : GeometricComponents k H) :
    geometricComponentMap k f c =
      ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map f).hom.hom.left.continuous.connectedComponentsMap c :=
  allComponentMap_apply _ c

@[simp]
theorem geometricComponentMap_id :
    geometricComponentMap k (𝟙 H) = MonoidHom.id (GeometricComponents k H) := by
  ext c
  change allComponentMap
    ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map (𝟙 H)) c = c
  rw [CategoryTheory.Functor.map_id, allComponentMap_id]
  rfl

@[simp]
theorem geometricComponentMap_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    geometricComponentMap k (f ≫ g) =
      (geometricComponentMap k g).comp (geometricComponentMap k f) := by
  ext c
  change allComponentMap
      ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map (f ≫ g)) c =
    allComponentMap ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map g)
      (allComponentMap ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map f) c)
  rw [CategoryTheory.Functor.map_comp, allComponentMap_comp]
  rfl

/-- Maps defined over k intertwine the full absolute Galois actions. -/
theorem geometricComponentMap_smul (f : H ⟶ H') (σ : Field.absoluteGaloisGroup k)
    (c : GeometricComponents k H) :
    geometricComponentMap k f (σ • c) = σ • geometricComponentMap k f c :=
  (allComponentConjugate_naturality k (AlgebraicClosure k) f σ c).symm

end Langlands.GroupScheme.IdentityComponent
