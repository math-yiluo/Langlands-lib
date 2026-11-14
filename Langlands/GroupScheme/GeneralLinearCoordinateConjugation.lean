import Langlands.GroupScheme.GeneralLinearAffineCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The representation on matrix and inverse-matrix coordinates by conjugation -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

section Matrices

variable (n : Type) [Fintype n] [DecidableEq n]
variable (A : Type u) [CommRing A]

/-- The matrix of conjugation on the direct sum of two matrix spaces. -/
def conjCoordsMatrixHom : GL n A →* Matrix (Coordinate n) (Coordinate n) A where
  toFun U := LinearMap.toMatrix' (conjCoordsLinear U)
  map_one' := by
    change LinearMap.toMatrix' (conjCoordsLinear (1 : GL n A)) = 1
    have h : conjCoordsLinear (1 : GL n A) = LinearMap.id :=
      LinearMap.ext (fun v => conjCoords_one v)
    rw [h, LinearMap.toMatrix'_id]
  map_mul' U V := by
    change LinearMap.toMatrix' (conjCoordsLinear (U * V)) =
      LinearMap.toMatrix' (conjCoordsLinear U) * LinearMap.toMatrix' (conjCoordsLinear V)
    rw [← LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' (LinearMap.ext (fun v => conjCoords_mul U V v))

/-- Invertible conjugation matrices, bundled as a group homomorphism. -/
def conjCoordsHom : GL n A →* GL (Coordinate n) A :=
  (conjCoordsMatrixHom n A).toHomUnits

@[simp] theorem conjCoordsHom_coe (U : GL n A) :
    (conjCoordsHom n A U : Matrix (Coordinate n) (Coordinate n) A) =
      LinearMap.toMatrix' (conjCoordsLinear U) := rfl

/-- The conjugation matrix has the advertised action on every coordinate vector. -/
@[simp] theorem conjCoordsHom_mulVec (U : GL n A) (v : Coordinate n → A) :
    (conjCoordsHom n A U : Matrix (Coordinate n) (Coordinate n) A) *ᵥ v =
      conjCoords U v :=
  LinearMap.toMatrix'_mulVec _ _

/-- On the values of an invertible matrix, the action is matrix conjugation. -/
theorem conjCoordsHom_mulVec_values (U g : GL n A) :
    (conjCoordsHom n A U : Matrix (Coordinate n) (Coordinate n) A) *ᵥ values g =
      values (U * g * U⁻¹) := by
  rw [conjCoordsHom_mulVec, values_conj]

variable {A} {B : Type v} [CommRing B]

/-- The conjugation matrices commute with every change of coefficients. -/
theorem conjCoordsHom_map (φ : A →+* B) (U : GL n A) :
    conjCoordsHom n B (Matrix.GeneralLinearGroup.map φ U) =
      Matrix.GeneralLinearGroup.map φ (conjCoordsHom n A U) := by
  apply Units.ext
  ext i j
  change conjCoords (Matrix.GeneralLinearGroup.map φ U) (Pi.single j 1) i =
    φ (conjCoords U (Pi.single j 1) i)
  have hs : (Pi.single j (1 : B)) = φ ∘ Pi.single j (1 : A) := by
    funext κ
    by_cases h : κ = j <;> simp [h]
  rw [hs, conjCoords_map]
  rfl

end Matrices

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- The natural conjugation action on coordinate vectors, on every scheme test. -/
def coordinateConjugationPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme n R).X) →* (T ⟶ (groupScheme (Coordinate n) R).X) :=
  (pointsEquiv (Coordinate n) R T).symm.toMonoidHom.comp
    ((conjCoordsHom n Γ(T.left, ⊤)).comp (pointsEquiv n R T).toMonoidHom)

@[simp] theorem pointsEquiv_coordinateConjugationPoints (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv (Coordinate n) R T (coordinateConjugationPoints n R T x) =
      conjCoordsHom n Γ(T.left, ⊤) (pointsEquiv n R T x) :=
  (pointsEquiv (Coordinate n) R T).apply_symm_apply _

/-- Naturality holds also for nonaffine test schemes. -/
theorem coordinateConjugationPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme n R).X) :
    coordinateConjugationPoints n R T' (a ≫ x) =
      a ≫ coordinateConjugationPoints n R T x := by
  apply (pointsEquiv (Coordinate n) R T').injective
  simp only [pointsEquiv_coordinateConjugationPoints, pointsEquiv_naturality,
    conjCoordsHom_map]

/-- The actual group-scheme representation on matrix and inverse-matrix coordinates. -/
def coordinateConjugationHom : groupScheme n R ⟶ groupScheme (Coordinate n) R :=
  homOfPoints (coordinateConjugationPoints n R)
    (coordinateConjugationPoints_naturality n R)

@[simp] theorem comp_coordinateConjugationHom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    x ≫ (coordinateConjugationHom n R).hom.hom = coordinateConjugationPoints n R T x :=
  comp_homOfPoints _ _ T x

/-- Its matrix over global sections is the conjugation matrix. -/
theorem pointsEquiv_coordinateConjugationHom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv (Coordinate n) R T (x ≫ (coordinateConjugationHom n R).hom.hom) =
      conjCoordsHom n Γ(T.left, ⊤) (pointsEquiv n R T x) := by
  rw [comp_coordinateConjugationHom, pointsEquiv_coordinateConjugationPoints]

/-- On all tests, its action on coordinate values is conjugation of invertible matrices. -/
theorem pointsEquiv_coordinateConjugationHom_mulVec (T : Over (Spec R))
    (x y : T ⟶ (groupScheme n R).X) :
    (pointsEquiv (Coordinate n) R T (x ≫ (coordinateConjugationHom n R).hom.hom) :
      Matrix (Coordinate n) (Coordinate n) Γ(T.left, ⊤)) *ᵥ values (pointsEquiv n R T y) =
        values (pointsEquiv n R T (x * y * x⁻¹)) := by
  rw [pointsEquiv_coordinateConjugationHom, conjCoordsHom_mulVec_values,
    map_mul, map_mul, map_inv]

/-- On an affine test the coefficients lie in the test algebra itself. -/
theorem affinePointsEquiv_coordinateConjugationHom (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    affinePointsEquiv (Coordinate n) R S (x ≫ (coordinateConjugationHom n R).hom.hom) =
      conjCoordsHom n S (affinePointsEquiv n R S x) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((functor (Coordinate n) R).map (Corepresented.affineSectionsIso S).inv)).1
  change Matrix.GeneralLinearGroup.map _ _ = Matrix.GeneralLinearGroup.map _ _
  rw [← pointsEquiv_eq_affinePointsEquiv, ← conjCoordsHom_map,
    ← pointsEquiv_eq_affinePointsEquiv]
  exact pointsEquiv_coordinateConjugationHom n R _ x

end Langlands.GroupScheme.GeneralLinear
