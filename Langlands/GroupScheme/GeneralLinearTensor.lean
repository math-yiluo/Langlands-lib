import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Multiplicative

/-! # The tensor-product morphism of general linear group schemes -/

noncomputable section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix Kronecker

namespace Langlands.GroupScheme.GeneralLinear

section Matrices

variable (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable (A : Type u) [CommRing A]

/-- The Kronecker operation, bundled as a homomorphism from the product group. -/
def kroneckerHom : GL n A × GL m A →* GL (n × m) A where
  toFun p := Matrix.GeneralLinearGroup.kronecker p.1 p.2
  map_one' := Units.ext Matrix.one_kronecker_one
  map_mul' p q := Units.ext (Matrix.mul_kronecker_mul p.1.val q.1.val p.2.val q.2.val)

@[simp] theorem kroneckerHom_apply (g : GL n A) (h : GL m A) :
    kroneckerHom n m A (g, h) = Matrix.GeneralLinearGroup.kronecker g h := rfl

@[simp] theorem kroneckerHom_coe (g : GL n A) (h : GL m A) :
    (kroneckerHom n m A (g, h) : Matrix (n × m) (n × m) A) =
      (g : Matrix n n A) ⊗ₖ (h : Matrix m m A) := rfl

/-- Entries of the tensor matrix are products of entries, in the ordered product basis. -/
theorem kroneckerHom_entry (g : GL n A) (h : GL m A) (i k : n) (j l : m) :
    kroneckerHom n m A (g, h) (i, j) (k, l) = g i k * h j l := rfl

variable {A} {B : Type v} [CommRing B]

/-- Kronecker matrices commute with every change of coefficients. -/
theorem kroneckerHom_map (f : A →+* B) (g : GL n A) (h : GL m A) :
    kroneckerHom n m B
        (Matrix.GeneralLinearGroup.map f g, Matrix.GeneralLinearGroup.map f h) =
      Matrix.GeneralLinearGroup.map f (kroneckerHom n m A (g, h)) := by
  apply Units.ext
  ext i k
  exact (map_mul f _ _).symm

/-- The tensor matrix acts on decomposable coordinate vectors by acting on both factors. -/
theorem kroneckerHom_mulVec (g : GL n A) (h : GL m A) (v : n → A) (w : m → A) :
    (kroneckerHom n m A (g, h) : Matrix (n × m) (n × m) A) *ᵥ
        (fun ij => v ij.1 * w ij.2) =
      fun ij => ((g : Matrix n n A) *ᵥ v) ij.1 * ((h : Matrix m m A) *ᵥ w) ij.2 := by
  funext ⟨i, j⟩
  exact (congrArg (fun M : Matrix (n × m) (Unit × Unit) A => M (i, j) ((), ()))
    (Matrix.mul_kronecker_mul (g : Matrix n n A) (fun i (_ : Unit) => v i)
      (h : Matrix m m A) (fun j (_ : Unit) => w j))).symm

end Matrices

variable (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable (R : CommRingCat.{u})

/-- The natural tensor operation on the points of the actual categorical product. -/
def tensorPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme n R ⊗ groupScheme m R).X) →*
      (T ⟶ (groupScheme (n × m) R).X) :=
  (pointsEquiv (n × m) R T).symm.toMonoidHom.comp
    ((kroneckerHom n m Γ(T.left, ⊤)).comp
      (((pointsEquiv n R T).toMonoidHom.prodMap (pointsEquiv m R T).toMonoidHom).comp
        (productPointsEquiv (groupScheme n R) (groupScheme m R) T).toMonoidHom))

@[simp] theorem pointsEquiv_tensorPoints (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    pointsEquiv (n × m) R T (tensorPoints n m R T x) =
      kroneckerHom n m Γ(T.left, ⊤)
        (pointsEquiv n R T (x ≫ fst (groupScheme n R).X (groupScheme m R).X),
          pointsEquiv m R T (x ≫ snd (groupScheme n R).X (groupScheme m R).X)) :=
  (pointsEquiv (n × m) R T).apply_symm_apply _

/-- Tensor points are natural for all morphisms of test schemes. -/
theorem tensorPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    tensorPoints n m R T' (a ≫ x) = a ≫ tensorPoints n m R T x := by
  apply (pointsEquiv (n × m) R T').injective
  simp only [pointsEquiv_tensorPoints, Category.assoc, pointsEquiv_naturality,
    kroneckerHom_map]

/-- The actual tensor-product homomorphism of general linear group schemes. -/
def tensorHom :
    groupScheme n R ⊗ groupScheme m R ⟶ groupScheme (n × m) R :=
  homOfPoints (tensorPoints n m R) (tensorPoints_naturality n m R)

@[simp] theorem comp_tensorHom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    x ≫ (tensorHom n m R).hom.hom = tensorPoints n m R T x :=
  comp_homOfPoints _ _ T x

/-- On any test scheme, the tensor morphism is the Kronecker matrix over global sections. -/
theorem pointsEquiv_tensorHom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    pointsEquiv (n × m) R T (x ≫ (tensorHom n m R).hom.hom) =
      kroneckerHom n m Γ(T.left, ⊤)
        (pointsEquiv n R T (x ≫ fst (groupScheme n R).X (groupScheme m R).X),
          pointsEquiv m R T (x ≫ snd (groupScheme n R).X (groupScheme m R).X)) := by
  rw [comp_tensorHom, pointsEquiv_tensorPoints]

/-- The actual scheme morphism preserves multiplication in every group of points. -/
theorem comp_tensorHom_mul (T : Over (Spec R))
    (x y : T ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    (x * y) ≫ (tensorHom n m R).hom.hom =
      (x ≫ (tensorHom n m R).hom.hom) * (y ≫ (tensorHom n m R).hom.hom) :=
  MonObj.mul_comp x y _

/-- Pairing two points and applying the tensor morphism takes their Kronecker product. -/
theorem pointsEquiv_lift_tensorHom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) (y : T ⟶ (groupScheme m R).X) :
    pointsEquiv (n × m) R T (lift x y ≫ (tensorHom n m R).hom.hom) =
      kroneckerHom n m Γ(T.left, ⊤) (pointsEquiv n R T x, pointsEquiv m R T y) := by
  rw [pointsEquiv_tensorHom]
  simp only [lift_fst, lift_snd]

/-- The entry formula holds for arbitrary, possibly nonaffine, test schemes. -/
theorem pointsEquiv_tensorHom_entry (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R ⊗ groupScheme m R).X) (i k : n) (j l : m) :
    pointsEquiv (n × m) R T (x ≫ (tensorHom n m R).hom.hom) (i, j) (k, l) =
      pointsEquiv n R T (x ≫ fst (groupScheme n R).X (groupScheme m R).X) i k *
        pointsEquiv m R T (x ≫ snd (groupScheme n R).X (groupScheme m R).X) j l := by
  rw [pointsEquiv_tensorHom]
  rfl

/-- Over global sections the actual tensor morphism has the decomposable-vector action. -/
theorem pointsEquiv_lift_tensorHom_mulVec (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) (y : T ⟶ (groupScheme m R).X)
    (v : n → Γ(T.left, ⊤)) (w : m → Γ(T.left, ⊤)) :
    (pointsEquiv (n × m) R T (lift x y ≫ (tensorHom n m R).hom.hom) :
        Matrix (n × m) (n × m) Γ(T.left, ⊤)) *ᵥ (fun ij => v ij.1 * w ij.2) =
      fun ij => ((pointsEquiv n R T x : Matrix n n Γ(T.left, ⊤)) *ᵥ v) ij.1 *
        ((pointsEquiv m R T y : Matrix m m Γ(T.left, ⊤)) *ᵥ w) ij.2 := by
  rw [pointsEquiv_lift_tensorHom]
  exact kroneckerHom_mulVec n m _ _ v w

/-- On affine test schemes, the tensor matrix has coefficients in the test algebra itself. -/
theorem affinePointsEquiv_tensorHom (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    affinePointsEquiv (n × m) R S (x ≫ (tensorHom n m R).hom.hom) =
      kroneckerHom n m S
        (affinePointsEquiv n R S (x ≫ fst (groupScheme n R).X (groupScheme m R).X),
          affinePointsEquiv m R S (x ≫ snd (groupScheme n R).X (groupScheme m R).X)) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((functor (n × m) R).map (Corepresented.affineSectionsIso S).inv)).1
  change Matrix.GeneralLinearGroup.map _ _ = Matrix.GeneralLinearGroup.map _ _
  rw [← pointsEquiv_eq_affinePointsEquiv, ← kroneckerHom_map,
    ← pointsEquiv_eq_affinePointsEquiv, ← pointsEquiv_eq_affinePointsEquiv]
  exact pointsEquiv_tensorHom n m R _ x

/-- The affine formula applied to a pair of points. -/
theorem affinePointsEquiv_lift_tensorHom (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X)
    (y : (algSpec R).obj (op S) ⟶ (groupScheme m R).X) :
    affinePointsEquiv (n × m) R S (lift x y ≫ (tensorHom n m R).hom.hom) =
      kroneckerHom n m S (affinePointsEquiv n R S x, affinePointsEquiv m R S y) := by
  rw [affinePointsEquiv_tensorHom]
  simp only [lift_fst, lift_snd]

/-- Entrywise affine coefficients of the actual tensor morphism. -/
theorem affinePointsEquiv_tensorHom_entry (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R ⊗ groupScheme m R).X)
    (i k : n) (j l : m) :
    affinePointsEquiv (n × m) R S (x ≫ (tensorHom n m R).hom.hom) (i, j) (k, l) =
      affinePointsEquiv n R S (x ≫ fst (groupScheme n R).X (groupScheme m R).X) i k *
        affinePointsEquiv m R S (x ≫ snd (groupScheme n R).X (groupScheme m R).X) j l := by
  rw [affinePointsEquiv_tensorHom]
  rfl

/-- The affine tensor formula commutes with all maps of test algebras. -/
theorem affinePointsEquiv_tensorHom_naturality {S S' : CommAlgCat.{u} R} (f : S ⟶ S')
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R ⊗ groupScheme m R).X) :
    affinePointsEquiv (n × m) R S'
        (((algSpec R).map f.op ≫ x) ≫ (tensorHom n m R).hom.hom) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (affinePointsEquiv (n × m) R S (x ≫ (tensorHom n m R).hom.hom)) := by
  rw [Category.assoc, affinePointsEquiv_naturality]

/-- On affine coordinates the tensor morphism acts separately on decomposable factors. -/
theorem affinePointsEquiv_lift_tensorHom_mulVec (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X)
    (y : (algSpec R).obj (op S) ⟶ (groupScheme m R).X) (v : n → S) (w : m → S) :
    (affinePointsEquiv (n × m) R S (lift x y ≫ (tensorHom n m R).hom.hom) :
        Matrix (n × m) (n × m) S) *ᵥ (fun ij => v ij.1 * w ij.2) =
      fun ij => ((affinePointsEquiv n R S x : Matrix n n S) *ᵥ v) ij.1 *
        ((affinePointsEquiv m R S y : Matrix m m S) *ᵥ w) ij.2 := by
  rw [affinePointsEquiv_lift_tensorHom]
  exact kroneckerHom_mulVec n m _ _ v w

end Langlands.GroupScheme.GeneralLinear
