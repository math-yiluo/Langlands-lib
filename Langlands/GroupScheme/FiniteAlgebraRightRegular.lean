import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.CorepresentedComultiplication
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The faithful inverse-right-regular representation of a finite algebra's units -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  {d : ℕ} (b : Module.Basis (Fin d) k A)

/-- Right multiplication by an element of the scalar-extended algebra, in the
base-changed basis. -/
def rightMulMatrix (R : Type u) [CommRing R] [Algebra k R] (x : R ⊗[k] A) :
    Matrix (Fin d) (Fin d) R :=
  LinearMap.toMatrix (b.baseChange R) (b.baseChange R) (LinearMap.mulRight R x)

theorem rightMulMatrix_apply (R : Type u) [CommRing R] [Algebra k R]
    (x : R ⊗[k] A) (i j : Fin d) :
    rightMulMatrix b R x i j = (b.baseChange R).repr ((b.baseChange R) j * x) i :=
  LinearMap.toMatrix_apply _ _ _ _ _

@[simp] theorem rightMulMatrix_one (R : Type u) [CommRing R] [Algebra k R] :
    rightMulMatrix b R 1 = 1 := by
  simp [rightMulMatrix, LinearMap.mulRight_one]

theorem rightMulMatrix_mul (R : Type u) [CommRing R] [Algebra k R]
    (x y : R ⊗[k] A) :
    rightMulMatrix b R (x * y) = rightMulMatrix b R y * rightMulMatrix b R x := by
  simp only [rightMulMatrix, LinearMap.mulRight_mul]
  exact LinearMap.toMatrix_comp (b.baseChange R) (b.baseChange R) (b.baseChange R) _ _

@[simp] theorem rightMulMatrix_add (R : Type u) [CommRing R] [Algebra k R]
    (x y : R ⊗[k] A) :
    rightMulMatrix b R (x + y) = rightMulMatrix b R x + rightMulMatrix b R y := by
  ext i j
  simp [rightMulMatrix_apply, mul_add]

theorem rightMulMatrix_injective (R : Type u) [CommRing R] [Algebra k R] :
    Function.Injective (rightMulMatrix b R) := by
  intro x y h
  have h' : LinearMap.mulRight R x = LinearMap.mulRight R y :=
    (LinearMap.toMatrix (b.baseChange R) (b.baseChange R)).injective h
  simpa using congrArg (fun f : (R ⊗[k] A) →ₗ[R] R ⊗[k] A => f 1) h'

/-- The matrix construction commutes with every change of scalar coefficients. -/
theorem rightMulMatrix_map {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (x : R ⊗[k] A) :
    rightMulMatrix b S (Algebra.TensorProduct.map f (AlgHom.id k A) x) =
      (rightMulMatrix b R x).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    ext i j
    simp [rightMulMatrix_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add, rightMulMatrix_add, hx, hy, Matrix.map_add _ (map_add _)]

/-- A unit acts on the algebra by multiplication on the right by its inverse.
The inverse makes this a left group representation. -/
def rightRegularUnits (R : Type u) [CommRing R] [Algebra k R] :
    (R ⊗[k] A)ˣ →* Matrix.GeneralLinearGroup (Fin d) R where
  toFun g :=
    { val := rightMulMatrix b R (g⁻¹ : (R ⊗[k] A)ˣ)
      inv := rightMulMatrix b R g
      val_inv := by rw [← rightMulMatrix_mul, Units.mul_inv, rightMulMatrix_one]
      inv_val := by rw [← rightMulMatrix_mul, Units.inv_mul, rightMulMatrix_one] }
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    simp only [mul_inv_rev, Units.val_mul, rightMulMatrix_mul])

theorem rightRegularUnits_injective (R : Type u) [CommRing R] [Algebra k R] :
    Function.Injective (rightRegularUnits b R) := by
  intro g h hgh
  apply inv_injective
  apply Units.ext
  exact rightMulMatrix_injective b R (congrArg Units.val hgh)

theorem rightRegularUnits_map {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (g : (R ⊗[k] A)ˣ) :
    rightRegularUnits b S
        (Units.map (Algebra.TensorProduct.map f (AlgHom.id k A)).toMonoidHom g) =
      Matrix.GeneralLinearGroup.map f.toRingHom (rightRegularUnits b R g) := by
  apply Units.ext
  exact rightMulMatrix_map b f (g⁻¹ : (R ⊗[k] A)ˣ)

/-- The inverse-right-regular representation on every relative test scheme. -/
def rightRegularPoints (T : Over (base k)) :
    (T ⟶ (groupScheme b).X) →*
      (T ⟶ (GeneralLinear.groupScheme (Fin d) (CommRingCat.of k)).X) :=
  (GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T).symm.toMonoidHom.comp
    ((rightRegularUnits b ((algΓ (CommRingCat.of k)).obj T).unop).comp
      (pointsEquiv b T).toMonoidHom)

theorem rightRegularPoints_matrix (T : Over (base k)) (x : T ⟶ (groupScheme b).X) :
    GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T (rightRegularPoints b T x) =
      rightRegularUnits b ((algΓ (CommRingCat.of k)).obj T).unop (pointsEquiv b T x) :=
  (GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T).apply_symm_apply _

theorem rightRegularPoints_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    rightRegularPoints b T' (a ≫ x) = a ≫ rightRegularPoints b T x := by
  apply (GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T').injective
  rw [GeneralLinear.pointsEquiv_naturality, rightRegularPoints_matrix,
    rightRegularPoints_matrix, pointsEquiv_naturality, rightRegularUnits_map]
  rfl

/-- The actual group-scheme representation on the finite-dimensional algebra. -/
def rightRegularRepresentation :
    MatrixRepresentation (groupScheme b) (Fin d) :=
  homOfPoints (rightRegularPoints b) (fun {_ _} a x => rightRegularPoints_naturality b a x)

theorem pointsEquiv_rightRegularRepresentation {T : Over (base k)}
    (x : T ⟶ (groupScheme b).X) :
    GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T
        (x ≫ (rightRegularRepresentation b).hom.hom) =
      rightRegularUnits b ((algΓ (CommRingCat.of k)).obj T).unop (pointsEquiv b T x) := by
  rw [rightRegularRepresentation, comp_homOfPoints, rightRegularPoints_matrix]

/-- Faithfulness on every test scheme makes the representation a monomorphism. -/
instance mono_rightRegularRepresentation_hom : Mono (rightRegularRepresentation b).hom.hom := by
  constructor
  intro T x y hxy
  apply (pointsEquiv b T).injective
  apply rightRegularUnits_injective b ((algΓ (CommRingCat.of k)).obj T).unop
  have h := congrArg (GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T) hxy
  simpa only [pointsEquiv_rightRegularRepresentation] using h

instance mono_rightRegularRepresentation_left :
    Mono (rightRegularRepresentation b).hom.hom.left :=
  Over.mono_left_of_mono _

/-- The regular representation as a natural transformation of actual unit functors. -/
def rightRegularNatTrans : functor k A ⟶ GeneralLinear.functor (Fin d) (CommRingCat.of k) where
  app R := GrpCat.ofHom (rightRegularUnits b R)
  naturality R S φ := by
    ext z
    exact rightRegularUnits_map b φ.hom z

/-- The actual right regular coefficient representation. -/
def rightRegularHom : MatrixRepresentation (groupScheme b) (Fin d) :=
  Corepresented.groupSchemeMap (corepresentableBy b)
    (GeneralLinear.corepresentableBy (Fin d) (CommRingCat.of k)) (rightRegularNatTrans b)

/-- The representation has its stated matrix on every affine coefficient point. -/
theorem rightRegularHom_affineMatrix (R : CommAlgCat.{u} (CommRingCat.of k))
    (z : (groupScheme b).affinePoints R) :
    (rightRegularHom b).affineMatrix R z = rightRegularUnits b R (affinePointsEquiv b R z) := by
  change Corepresented.affinePointsEquiv _
    (GeneralLinear.corepresentableBy (Fin d) (CommRingCat.of k)) R
    (z ≫ (rightRegularHom b).hom.hom) = _
  rw [rightRegularHom, Corepresented.groupSchemeMap_affinePoints]
  rfl

/-- The regular representation is a monomorphism on actual relative schemes. -/
instance mono_rightRegularHom : Mono (rightRegularHom b).hom.hom := by
  constructor
  intro T f g he
  apply (pointsEquiv b T).injective
  apply rightRegularUnits_injective b (((algΓ (CommRingCat.of k)).obj T).unop)
  have hh := congrArg (Corepresented.pointsEquiv _
    (GeneralLinear.corepresentableBy (Fin d) (CommRingCat.of k)) T) he
  rw [rightRegularHom, Corepresented.groupSchemeMap_points,
    Corepresented.groupSchemeMap_points] at hh
  exact hh

end Langlands.GroupScheme.FiniteAlgebraUnits
