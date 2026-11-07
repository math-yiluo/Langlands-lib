import Langlands.GroupScheme.SpecialLinearWeilRootGroups
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Actual tensor point models of restricted special-linear roots -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SpecialLinear.Root

variable {n : Type} [Fintype n] [DecidableEq n]
  (R : CommRingCat.{u}) {i j : n}

/-- The actual coordinate-root map is the scalar transvection on affine coefficient points. -/
theorem affinePointsEquiv_rootMap (hij : i ≠ j) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (VectorGroup.groupScheme R 1).X) :
    SpecialLinear.affinePointsEquiv n R S (x ≫ (rootMap R hij).hom.hom) =
      Matrix.SpecialLinearGroup.transvection hij
        ((Corepresented.affinePointsEquiv (VectorGroup.functor R 1)
          (VectorGroup.corepresentableBy R 1) S x).toAdd 0) := by
  have h := pointsEquiv_rootMap R hij ((algSpec R).obj (op S)) x
  have hm := congrArg
    (Matrix.SpecialLinearGroup.map (Corepresented.affineSectionsIso S).hom.hom.toRingHom) h
  erw [map_transvection (n := n)
    (Corepresented.affineSectionsIso S).hom.hom.toRingHom hij] at hm
  have hsl := Corepresented.map_affineSectionsIso_pointsEquiv
    (SpecialLinear.functor n R) (SpecialLinear.corepresentableBy n R) S
      (x ≫ (rootMap R hij).hom.hom)
  change Matrix.SpecialLinearGroup.map _
      (SpecialLinear.pointsEquiv n R _ (x ≫ (rootMap R hij).hom.hom)) =
    SpecialLinear.affinePointsEquiv n R S (x ≫ (rootMap R hij).hom.hom) at hsl
  erw [hsl] at hm
  have hv := Corepresented.map_affineSectionsIso_pointsEquiv
    (VectorGroup.functor R 1) (VectorGroup.corepresentableBy R 1) S x
  have hx := congrArg (fun z : Multiplicative (Fin 1 → S) => z.toAdd 0) hv
  change (Corepresented.affineSectionsIso S).hom.hom
    ((VectorGroup.coordinates R 1 _ x).toAdd 0) = _ at hx
  erw [hx] at hm
  exact hm

end Langlands.GroupScheme.SpecialLinear.Root

namespace Langlands.GroupScheme.SpecialLinear.WeilRoot

variable {n : Type} [Fintype n] [DecidableEq n]
  (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

attribute [local instance] specialLinear_affine specialLinear_finiteType
  vectorGroup_affine vectorGroup_finiteType

/-- The actual relative global-section algebra of a test scheme. -/
abbrev sectionAlgebra (T : Over (Spec (CommRingCat.of F))) :
    CommAlgCat.{u} (CommRingCat.of F) :=
  ((algΓ (CommRingCat.of F)).obj T).unop

/-- Tensor extension of the actual relative global-section algebra. -/
abbrev tensorAlgebra (T : Over (Spec (CommRingCat.of F))) :
    CommAlgCat.{u} (CommRingCat.of E) :=
  (AffineWeil.tensorFunctor F E).obj (sectionAlgebra F T)

/-- All test points of the actual restricted group are matrices over the tensor algebra. -/
def tensorMatrixEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme (n := n) F E).X) ≃*
      Matrix.SpecialLinearGroup n (tensorAlgebra F E T) :=
  (Corepresented.pointsEquiv
    (AffineWeil.pointFunctor F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
    (AffineWeil.corepresentableBy F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
    T).trans
      (SpecialLinear.affinePointsEquiv n (CommRingCat.of E) (tensorAlgebra F E T))

/-- All restricted additive-root points are their actual tensor-valued scalar coordinates. -/
def tensorRootCoordinates (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (additiveScheme F E).X) ≃* Multiplicative (Fin 1 → tensorAlgebra F E T) :=
  (Corepresented.pointsEquiv
    (AffineWeil.pointFunctor F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
    (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
    T).trans
      (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of E) 1)
        (VectorGroup.corepresentableBy (CommRingCat.of E) 1) (tensorAlgebra F E T))

/-- The tensor coefficient map induced by an actual change of relative test scheme. -/
def tensorMap {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T) :
    tensorAlgebra F E T →+* tensorAlgebra F E T' :=
  ((AffineWeil.tensorFunctor F E).map
    ((algΓ (CommRingCat.of F)).map a).unop).hom.toRingHom

/-- The actual restricted matrix coordinates respect every change of test scheme. -/
theorem tensorMatrixEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme (n := n) F E).X) :
    tensorMatrixEquiv F E T' (a ≫ x) =
      Matrix.SpecialLinearGroup.map (tensorMap F E a) (tensorMatrixEquiv F E T x) := by
  change SpecialLinear.affinePointsEquiv n (CommRingCat.of E) (tensorAlgebra F E T')
      (Corepresented.pointsEquiv
        (AffineWeil.pointFunctor F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
        (AffineWeil.corepresentableBy F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
        T' (a ≫ x)) =
    Matrix.SpecialLinearGroup.map (tensorMap F E a)
      (SpecialLinear.affinePointsEquiv n (CommRingCat.of E) (tensorAlgebra F E T)
        (Corepresented.pointsEquiv
          (AffineWeil.pointFunctor F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
          (AffineWeil.corepresentableBy F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
          T x))
  erw [Corepresented.pointsEquiv_naturality
    (AffineWeil.pointFunctor F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
    (AffineWeil.corepresentableBy F E (SpecialLinear.groupScheme n (CommRingCat.of E))) a x]
  exact Corepresented.affinePointsEquiv_naturality
    (SpecialLinear.functor n (CommRingCat.of E))
    (SpecialLinear.corepresentableBy n (CommRingCat.of E))
    ((AffineWeil.tensorFunctor F E).map ((algΓ (CommRingCat.of F)).map a).unop) _

/-- Restricted root coordinates respect every change of test scheme. -/
theorem tensorRootCoordinates_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (x : T ⟶ (additiveScheme F E).X) :
    (tensorRootCoordinates F E T' (a ≫ x)).toAdd 0 =
      tensorMap F E a ((tensorRootCoordinates F E T x).toAdd 0) := by
  change (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of E) 1)
      (VectorGroup.corepresentableBy (CommRingCat.of E) 1) (tensorAlgebra F E T')
      (Corepresented.pointsEquiv
        (AffineWeil.pointFunctor F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
        (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
        T' (a ≫ x))).toAdd 0 =
    tensorMap F E a
      ((Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of E) 1)
        (VectorGroup.corepresentableBy (CommRingCat.of E) 1) (tensorAlgebra F E T)
        (Corepresented.pointsEquiv
          (AffineWeil.pointFunctor F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
          (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
          T x)).toAdd 0)
  erw [Corepresented.pointsEquiv_naturality
    (AffineWeil.pointFunctor F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
    (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1)) a x]
  have h := Corepresented.affinePointsEquiv_naturality
    (VectorGroup.functor (CommRingCat.of E) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of E) 1)
    ((AffineWeil.tensorFunctor F E).map ((algΓ (CommRingCat.of F)).map a).unop)
    (Corepresented.pointsEquiv
      (AffineWeil.pointFunctor F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
      (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
      T x)
  exact congrArg (fun z : Multiplicative (Fin 1 → tensorAlgebra F E T') => z.toAdd 0) h

/-- On every test scheme the actual restricted root morphism is the tensor transvection. -/
theorem tensorMatrixEquiv_rootMap {i j : n} (hij : i ≠ j)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ (additiveScheme F E).X) :
    tensorMatrixEquiv F E T (x ≫ (rootMap F E hij).hom.hom) =
      Matrix.SpecialLinearGroup.transvection hij ((tensorRootCoordinates F E T x).toAdd 0) := by
  change SpecialLinear.affinePointsEquiv n (CommRingCat.of E) (tensorAlgebra F E T)
      (Corepresented.pointsEquiv
        (AffineWeil.pointFunctor F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
        (AffineWeil.corepresentableBy F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
        T (x ≫ (AffineWeil.map F E (Root.rootMap (CommRingCat.of E) hij)).hom.hom)) =
    Matrix.SpecialLinearGroup.transvection hij
      ((Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of E) 1)
        (VectorGroup.corepresentableBy (CommRingCat.of E) 1) (tensorAlgebra F E T)
        (Corepresented.pointsEquiv
          (AffineWeil.pointFunctor F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
          (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
          T x)).toAdd 0)
  erw [Corepresented.groupSchemeMap_points
    (AffineWeil.corepresentableBy F E (VectorGroup.groupScheme (CommRingCat.of E) 1))
    (AffineWeil.corepresentableBy F E (SpecialLinear.groupScheme n (CommRingCat.of E)))
    (AffineWeil.pointTransformation F E (Root.rootMap (CommRingCat.of E) hij)) x]
  exact Root.affinePointsEquiv_rootMap (CommRingCat.of E) hij (tensorAlgebra F E T) _

end Langlands.GroupScheme.SpecialLinear.WeilRoot
